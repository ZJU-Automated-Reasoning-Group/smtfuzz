"""Seed-based SMT fuzzing runner"""

import argparse
import glob
import hashlib
import logging
import os
import random
import shutil
import subprocess
import time
from threading import Timer
import tqdm

from smtfuzz.runner.base import BaseRunner
from smtfuzz.bet.op_mutator import StringMutation


class SeedRunner(BaseRunner):
    """Runner for seed-based SMT fuzzing"""
    
    def __init__(self):
        super().__init__()
        self.m_test_invalid_model = True
        self.m_has_z3py = True
        
        try:
            from smtfuzz.bet.bet_mutator import Z3Mutation
        except Exception as e:
            print(e)
            print("No z3py, will use StrMut or TyMut")
            self.m_has_z3py = False
    
    def setup_args(self):
        """Setup command line arguments specific to seed runner"""
        parser = argparse.ArgumentParser(description="SMT Seed-based Fuzzing Runner")
        self.setup_common_args(parser)
        
        # Seed-specific arguments
        parser.add_argument('--seed', dest='seed', default='no', type=str, help="Seed directory path")
        parser.add_argument('--diff', dest='diff', default='no', type=str, help="Enable differential testing")
        parser.add_argument('--perf', dest='perf', default='no', type=str, help="Enable performance testing")
        parser.add_argument('--nomut', dest='nomut', default='no', type=str, help="Disable mutation")
        parser.add_argument('--solvers', dest='solvers', default='no', type=str, help="Semicolon-separated solver list")
        parser.add_argument('--formula_injection', dest='formula_injection', default='none', type=str, help="Formula injection mode")
        
        return parser
    
    def profile_worker(self, pack):
        """Profile worker for measuring mutation speed"""
        solver, tmp_file, outdir = pack
        
        if os.stat(tmp_file).st_size == 0:
            return
            
        try:
            if self.statistic:
                self.statistic.seeds += 1
                self.statistic.printbar()
                
            logging.debug("Start to mutate")
            counter = hashlib.md5(tmp_file.encode('utf-8')).hexdigest()
            name = f'/muta_input-0_{counter[:6]}_'
            gene = StringMutation(tmp_file)
            
            for i in range(self.args.count):
                tmp_start = time.time()
                tmp_file_mut = os.path.join(outdir, 'input', f"{name}{i}.smt2")
                
                try:
                    with open(tmp_file_mut, 'w') as mut:
                        if gene.generate(tmp_file_mut):
                            logging.debug("mutate success")
                        else:
                            if os.path.isfile(tmp_file_mut):
                                os.remove(tmp_file_mut)
                            break
                except Exception as file_e:
                    print(file_e)
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)
                    continue
                    
                tmp_end = time.time()
                if self.statistic:
                    self.statistic.profile_data.append(tmp_end - tmp_start)
                    self.statistic.mutants += 1
                    
        except Exception as ee:
            print(ee)
    
    def worker(self, pack):
        """Main worker for seed-based fuzzing"""
        solver, tmp_file, outdir = pack
        
        if os.stat(tmp_file).st_size == 0:
            return
            
        # Setup solver command
        cmd_tool = self._setup_solver_command(solver)
        if not cmd_tool:
            return
            
        try:
            # Test seed file first
            if not self._test_seed_file(tmp_file, cmd_tool, outdir):
                return
                
            if self.args.nomut == "yes":
                return
                
            # Start mutation
            self._mutate_and_test(tmp_file, cmd_tool, outdir)
            
        except Exception as ee:
            print(ee)
    
    def worker_diff(self, pack):
        """Worker for differential testing"""
        solver, tmp_file, outdir = pack
        
        if os.stat(tmp_file).st_size == 0:
            print("tmp file empty")
            return
            
        counter = hashlib.md5(tmp_file.encode('utf-8')).hexdigest()
        name = f'/muta_input-0_{counter[:6]}_'
        
        # Setup mutation
        gene = StringMutation(tmp_file)
        if self.args.solvermode == 'unsat_core':
            gene.enable_unsat_core()
        if self.args.solvermode == 'proof':
            gene.enable_proof()
        if self.args.solvermode == 'smtopt':
            gene.enable_smtopt()
            
        if self.statistic:
            self.statistic.seeds += 1
            
        for i in range(self.args.count):
            tmp_file_mut = os.path.join(outdir, 'input', f"{name}{i}.smt2")
            
            try:
                with open(tmp_file_mut, 'w') as mut:
                    if self.args.solvermode == 'exp' and self.m_has_z3py:
                        bet_mutator_path = os.path.join(os.path.dirname(__file__), '../../examples/mutators/bet_mutator.py')
                        if not self.try_z3_mutate(tmp_file, tmp_file_mut, bet_mutator_path):
                            if os.path.isfile(tmp_file_mut):
                                os.remove(tmp_file_mut)
                            break
                    else:
                        if gene.generate(tmp_file_mut):
                            logging.debug("mutate success")
                        else:
                            if os.path.isfile(tmp_file_mut):
                                os.remove(tmp_file_mut)
                            break
            except Exception as file_e:
                if os.path.isfile(tmp_file_mut):
                    os.remove(tmp_file_mut)
                continue
                
            if self.statistic:
                self.statistic.mutants += 1
                self.statistic.printbar()
                
            # Test with multiple solvers
            self._differential_test(tmp_file_mut, tmp_file, outdir, name)
    
    def _setup_solver_command(self, solver):
        """Setup solver command based on solver type"""
        cmd_tool = []
        solver_map = {
            'yices': self.get_smt_solver_path("yices"),
            'cvc5': self.get_smt_solver_path("cvc5"),
            'z3': self.get_smt_solver_path("z3"),
            'open': self.get_smt_solver_path("open"),
            'pol': self.get_smt_solver_path("pol")
        }
        
        to_test = solver_map.get(solver, solver)
        cmd_tool = to_test.split(' ')
        
        # Add solver-specific options
        if 'cvc' in to_test:
            cmd_tool.extend(['--quiet', '--incremental', '--check-models'])
            if self.args.solvermode == 'unsat_core':
                cmd_tool.append('--check-unsat-cores')
        elif 'yice' in to_test or 'boolec' in to_test:
            cmd_tool.append('--incremental')
            
        return cmd_tool
    
    def _test_seed_file(self, tmp_file, cmd_tool, outdir):
        """Test the seed file with the solver"""
        cmd_seed = cmd_tool + [tmp_file]
        logging.debug("Seed res: ")
        logging.debug(cmd_seed)
        
        env = os.environ.copy()
        if any(solver in ' '.join(cmd_tool) for solver in ['cvc', 'open']):
            env["ASAN_OPTIONS"] = "log_path=stdout:" + env.get("ASAN_OPTIONS", "")
            env["ASAN_OPTIONS"] += "detect_leaks=0"
            
        ptool = subprocess.Popen(cmd_seed, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
        is_timeout = [False]
        timertool = Timer(10, self.terminate_process, args=[ptool, is_timeout])
        timertool.start()
        
        try:
            out_seed = ptool.stdout.readlines()
            out_seed = ' '.join([str(element.decode('UTF-8')) for element in out_seed])
            logging.debug(out_seed)
            
            if is_timeout[0]:
                return False
            elif any(keyword in out_seed for keyword in ["unknown", "error", "Error"]):
                return False
            elif any(keyword in out_seed for keyword in ["Santi", 'ASSERTION', 'Assert', 'Fat']) or \
                 (self.m_test_invalid_model and 'invalid mo' in out_seed):
                if self._check_error_against_blacklist(out_seed):
                    print("find error!")
                    print("seed cmd: ", cmd_seed)
                    print("seed res: ", out_seed)
                    print("seed: ", tmp_file)
                    shutil.copy(tmp_file, os.path.join(outdir, "crash"))
                    return False
                    
        finally:
            ptool.stdout.close()
            timertool.cancel()
            
        if self.statistic:
            self.statistic.seeds += 1
            
        return True
    
    def _mutate_and_test(self, tmp_file, cmd_tool, outdir):
        """Mutate the seed file and test mutations"""
        solver_opts = [" "]
        if self.args.optfuzz == 'yes':
            if self.args.solver == 'z3':
                solver_opts = ["NA"]
            elif self.args.solver == 'cvc5':
                solver_opts = ["NA", "--cegqi", "--strings-exp", "--fmf-fun"]
            elif self.args.solver == 'yices':
                solver_opts = ["NA", "--mcsat"]
                
        counter = hashlib.md5(tmp_file.encode('utf-8')).hexdigest()
        cmd_ori = cmd_tool[:-1]  # Remove the file argument
        
        for opt_id, opt in enumerate(solver_opts, 1):
            cmd_new = cmd_ori.copy()
            if len(solver_opts) > 1 and opt != "NA":
                cmd_new.append(opt)
                
            name = f'/muta_input-0_{opt_id}_{counter[:6]}_'
            gene = StringMutation(tmp_file)
            
            # Configure mutation based on solver mode
            if self.args.solvermode == 'unsat_core':
                gene.enable_unsat_core()
            elif self.args.solvermode == 'proof':
                gene.enable_proof()
            elif self.args.solvermode == 'smtopt':
                gene.enable_smtopt()
                
            if self.args.optfuzz == 'yes':
                if self.args.solver == "cvc5":
                    gene.enable_cvc4_option()
                elif self.args.solver == "z3":
                    gene.enable_z3_option()
                    
            for i in range(self.args.count):
                tmp_file_mut = os.path.join(outdir, 'input', f"{name}{i}.smt2")
                
                try:
                    with open(tmp_file_mut, 'w') as mut:
                        if self.args.solvermode == 'exp' and self.m_has_z3py:
                            bet_mutator_path = os.path.join(os.path.dirname(__file__), '../../examples/mutators/bet_mutator.py')
                            if not self.try_z3_mutate(tmp_file, tmp_file_mut, bet_mutator_path):
                                if os.path.isfile(tmp_file_mut):
                                    os.remove(tmp_file_mut)
                                break
                        else:
                            if gene.generate(tmp_file_mut):
                                logging.debug("mutate success")
                            else:
                                if os.path.isfile(tmp_file_mut):
                                    os.remove(tmp_file_mut)
                                break
                except Exception as file_e:
                    print(file_e)
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)
                    continue
                    
                if self.statistic:
                    self.statistic.mutants += 1
                    self.statistic.printbar()
                    
                # Test the mutation
                if self._test_mutation(tmp_file_mut, cmd_new, outdir, name):
                    break  # Found an error, move to next mutation
    
    def _test_mutation(self, tmp_file_mut, cmd_mut, outdir, name):
        """Test a single mutation"""
        cmd_mut_full = cmd_mut + [tmp_file_mut]
        logging.debug(cmd_mut_full)
        
        env = os.environ.copy()
        if any(solver in ' '.join(cmd_mut) for solver in ['cvc', 'open']):
            env["ASAN_OPTIONS"] = "log_path=stdout:" + env.get("ASAN_OPTIONS", "")
            env["ASAN_OPTIONS"] += "detect_leaks=0"
            
        pmut = subprocess.Popen(cmd_mut_full, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
        is_timeout = [False]
        timermut = Timer(5, self.terminate_process, args=[pmut, is_timeout])
        timermut.start()
        
        try:
            out_mut = pmut.stdout.readlines()
            out_mut = ' '.join([str(element.decode('UTF-8')) for element in out_mut])
            logging.debug("Mut res: ")
            logging.debug(out_mut)
            
            bl_msg = ['unsupported', 'what', 'Warning', 'suppress', 'unknown', 'support', 'type', 'Unes']
            
            if any(keyword in out_mut for keyword in ["Santi", 'ASSERTION', 'Assert', 'Fat']) or \
               (self.m_test_invalid_model and 'invalid mo' in out_mut):
                if self._check_error_against_blacklist(out_mut):
                    # Additional check for non-crash errors
                    if "Santi" not in out_mut:
                        for blm in bl_msg:
                            if blm in out_mut:
                                return False
                                
                    if self.statistic:
                        self.statistic.error += 1
                        
                    print("find error!")
                    print("mut cmd: ", cmd_mut_full)
                    print("mut res: ", out_mut)
                    crash_file = os.path.join(outdir, 'crash', f"{name}.smt2")
                    print("mut: ", crash_file)
                    shutil.copy(tmp_file_mut, crash_file)
                    return True
            else:
                if os.path.isfile(tmp_file_mut):
                    os.remove(tmp_file_mut)
                    
        finally:
            pmut.stdout.close()
            timermut.cancel()
            
        return False
    
    def _differential_test(self, tmp_file_mut, tmp_file, outdir, name):
        """Perform differential testing with multiple solvers"""
        m_tools = [
            self.get_smt_solver_path("z3"),
            self.get_smt_solver_path("z3") + " rewriter.flat=false",
            self.get_smt_solver_path("z3") + " smt.arith.solver=2",
            self.get_smt_solver_path("cvc5")
        ]
        
        if self.args.solvers != "no":
            m_tools = self.args.solvers.split(";")
            
        try:
            m_res_out = []
            m_res_tout = []
            
            for tool in m_tools:
                cmd_tool = tool.split(' ')
                
                if 'cvc' in tool:
                    cmd_tool.append('--quiet')
                if any(solver in tool for solver in ['yice', 'cvc', 'boolec']):
                    cmd_tool.append('--incremental')
                    
                env = os.environ.copy()
                env["ASAN_OPTIONS"] = "log_path=stdout:" + env.get("ASAN_OPTIONS", "")
                env["ASAN_OPTIONS"] += "detect_leaks=0"
                
                cmd_tool.append(tmp_file_mut)
                logging.debug(cmd_tool)
                
                ptool = subprocess.Popen(cmd_tool, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
                is_timeout = [False]
                timertool = Timer(10, self.terminate_process, args=[ptool, is_timeout])
                timertool.start()
                
                try:
                    out_tool = ptool.stdout.readlines()
                    out_tool = ' '.join([str(element.decode('UTF-8')) for element in out_tool])
                    
                    if not is_timeout[0]:
                        m_res_tout.append(False)
                        logging.debug(out_tool)
                        
                        bl_msg = ['non-diff', 'unsupported', 'Warning', 'suppress', 'unknown', 'ASSERTION', 'Ass',
                                 'ignoring uns', 'not supported', 'Exception', 'Sant', 'Fat', 'inv',
                                 'not defined', 'terminate', 'error', 'suffer', 'Segment', 'Error', 'Invalid',
                                 'Unexpected']
                        
                        if not any(bl in out_tool for bl in bl_msg):
                            m_res_out.append(out_tool)
                    else:
                        if not any(keyword in out_tool for keyword in ['true', 'false', 'error', 'an inv', 'Ass', 'ASSERTION']):
                            m_res_tout.append(True)
                            
                finally:
                    ptool.stdout.close()
                    timertool.cancel()
                    
            # Check for inconsistencies
            if 2 <= len(m_res_out) != m_res_out.count(m_res_out[0]) and '(' not in m_res_out[0]:
                print("find inconsistency!")
                print(tmp_file_mut)
                shutil.copyfile(tmp_file, os.path.join(outdir, 'crash', name))
                return True
            elif self.args.perf == "yes" and m_res_tout.count(True) == 1:
                print("find timeout!")
                print(tmp_file_mut)
                return True
            else:
                if os.path.isfile(tmp_file_mut):
                    os.remove(tmp_file_mut)
                    
        except Exception as ee:
            print(ee)
            
        return False
    
    def _check_error_against_blacklist(self, output):
        """Check if error should be reported based on blacklist"""
        for item in self.black_list:
            if item and item in output:
                return False
        return True
    
    def run(self):
        """Main run method for seed-based fuzzing"""
        parser = self.setup_args()
        args = parser.parse_args()
        
        self.initialize(args)
        
        if args.seed == 'no':
            print("Please specify the seed path!")
            self.cleanup()
            return
            
        # Setup output directory
        crashes, inputs = self.setup_output_directory(args.output)
        
        # Find seed files
        seed_files = glob.glob(os.path.join(args.seed, '**/*.smt2'), recursive=True)
        random.shuffle(seed_files)
        tasks = [(args.solver, f, args.output) for f in seed_files]
        
        # Run fuzzing
        try:
            if args.profile:
                for _ in tqdm.tqdm(self.pool.imap_unordered(self.profile_worker, tasks), total=len(tasks)):
                    pass
            elif args.diff == 'yes':
                for _ in tqdm.tqdm(self.pool.imap_unordered(self.worker_diff, tasks), total=len(tasks)):
                    pass
            else:
                for _ in tqdm.tqdm(self.pool.imap_unordered(self.worker, tasks), total=len(tasks)):
                    pass
        finally:
            self.cleanup()
            print("We finish here, have a good day!")


def main():
    """Main entry point for seed runner"""
    runner = SeedRunner()
    runner.run()


if __name__ == "__main__":
    main() 