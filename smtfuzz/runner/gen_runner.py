"""Generation-based SMT fuzzing runner"""

import argparse
import configparser
import hashlib
import logging
import os
import random
import shutil
import subprocess
import sys
from threading import Timer

from .base import BaseRunner
from smtfuzz.bet.op_mutator import StringMutation


# Logic definitions
fuzzsmt_logics = ['QF_LRA', 'QF_AUFLIA', 'QF_AX', 'QF_BV', 'QF_IDL', 'QF_LIA',
                  'QF_NIA', 'QF_NRA', 'QF_UF', 'QF_UFBV', 'QF_UFIDL', 'QF_UFLIA', 'QF_UFLRA',
                  'QF_UFNRA', 'QF_UFRDL', 'AUFLIA', 'AUFLIRA', 'AUFNIRA']

qf_int_logic_options = ['QF_IDL', 'QF_NIA', 'QF_LIA', 'QF_ANIA', 'QF_ALIA', 'QF_AUFNIA', 'QF_AUFLIA', 'QF_UFNIA',
                        'QF_UFLIA']
q_int_logic_options = ['ALIA', 'ANIA', 'LIA', 'NIA', 'UFLIA', 'UFNIA', 'AUFLIA', 'AUFNIA']
int_logic_options = qf_int_logic_options + q_int_logic_options

qf_real_logic_options = ['QF_RDL', 'QF_UFLRA', 'QF_NRA', 'QF_LRA', 'QF_UFNRA', 'QF_AUFNRA', 'QF_AUFLRA']
q_real_logic_options = ['LRA', 'NRA', 'UFLRA', 'UFNRA', 'AUFLRA', 'AUFNRA']
real_logic_options = qf_real_logic_options + q_real_logic_options

qf_bv_logic_options = ['QF_BV', 'QF_UFBV', 'QF_ABV', 'QF_AUFBV']
q_bv_logic_options = ['BV', 'UFBV', 'ABV', 'AUFBV']
bv_logic_options = qf_bv_logic_options + q_bv_logic_options

qf_logic_options = qf_int_logic_options + qf_real_logic_options + qf_bv_logic_options
qf_logic_options.append('BOOL')
q_logic_options = q_int_logic_options + q_real_logic_options + q_bv_logic_options
q_logic_options.append('QBF')

bool_logic_options = ['QF_BOOL', 'QBF', 'QF_UF', 'UF']
other_logic_options = ['BVINT', 'QF_AX', 'SET', 'QF_FP', 'QF_FPLRA', 'FP', 'FPLRA', 'QF_S', 'QF_SLIA', 'QF_SNIA', 'ALL']

uf_logic_options = ['QF_UF', 'QF_UFLIA', 'QF_UFLRA', 'QF_UFNRA', 'QF_UFNIA', 'QF_AUFLIA', 'QF_AUFLRA', 'QF_AUFNIA',
                    'QF_AUFNRA', 'QF_UFC', 'QF_UFLIRA', 'QF_UFNIRA', 'QF_AUFLIRA', 'QF_AUFNIRA']
uf_logic_options += ['UF', 'UFLIA', 'UFLRA', 'UFNRA', 'UFNIA', 'AUFLIA', 'AUFLRA', 'AUFNIA', 'AUFNRA', 'UFC', 'UFLIRA',
                     'UFNIRA', 'AUFLIRA', 'AUFNIRA']

lira_logics = ['QF_LIRA', 'LIRA', 'QF_ALIRA', 'ALIRA', 'QF_UFLIRA', 'UFLIRA', 'QF_AUFLIRA', 'AUFLIRA']
nira_logics = ['QF_NIRA', 'NIRA', 'QF_ANIRA', 'ANIRA', 'QF_UFNIRA', 'UFNIRA', 'QF_AUFNIRA', 'AUFNIRA']
ira_logics = lira_logics + nira_logics

qfla_logics = ['QF_LIRA', 'QF_ALIRA', 'QF_UFLIRA', 'QF_LIA', 'QF_ALIA', 'QF_AUFLIA', 'QF_UFLIA', 'QF_UFLRA', 'QF_LRA',
               'QF_AUFLR']
qla_logics = ['ALIA', 'LIA', 'UFLIA', 'AUFLIA', 'LRA', 'UFLRA', 'AUFLRA', 'LIRA', 'UFLIRA', 'AUFLIRA']
la_logics = qfla_logics + qla_logics

all_logic_options = []
all_logic_options += qf_logic_options
all_logic_options += q_logic_options
all_logic_options += bool_logic_options
all_logic_options += other_logic_options
all_logic_options += ira_logics

strategies = ['noinc', 'noinc', 'CNFexp', 'cnf', 'ncnf', 'bool', 'bool']


class GenRunner(BaseRunner):
    """Runner for generation-based SMT fuzzing"""
    
    def __init__(self):
        super().__init__()
        self.m_has_z3py = True
        self.m_test_maxsmt = False
        self.generator = 'generator.py'
        
        try:
            from smtfuzz.bet.bet_mutator import Z3Mutation
        except Exception as e:
            print("No z3py, will use StrMut or TyMut")
            self.m_has_z3py = False
    
    def setup_args(self):
        """Setup command line arguments specific to generation runner"""
        parser = argparse.ArgumentParser(description="SMT Generation-based Fuzzing Runner")
        self.setup_common_args(parser)
        
        return parser
    
    def gen_and_mut(self, idt):
        """Generate and mutate SMT formulas"""
        counter = 0
        
        while True:
            try:
                # Parameter generation logic
                if counter % self.args.count == 0:
                    if self.args.solvermode in ["default", "exp", "proof", "interpolant", "unsat_core"]:
                        cnfratio = random.randint(2, 50)
                        cntsize = random.randint(25, 550)
                        strategy = random.randint(0, len(strategies) - 1)
                        
                        if self.args.solvermode == "exp":
                            strategy = 0
                            
                        logiclist = self._get_logic_list()
                        logic = random.randint(0, len(logiclist) - 1)
                        
                    elif self.args.solvermode in ["smtopt", "maxsmt"]:
                        cnfratio = random.randint(2, 25)
                        cntsize = random.randint(3, 120)
                        strategy = random.randint(0, len(strategies) - 1)
                        
                        logiclist = self._get_logic_list_qf()
                        logic = random.randint(0, len(logiclist) - 1)
                        
                    counter = 0
                    
                final_logic_to_use = logiclist[logic]
                
                # Allow fixed logic selection
                if self.args.logicmode in all_logic_options:
                    final_logic_to_use = self.args.logicmode
                    
                name = f'diff_input-{idt}_{counter}_{strategies[strategy]}_{cnfratio}_{cntsize}_{final_logic_to_use}.smt2'
                tmp_file = os.path.join(self.args.output, 'input', name)
                
                counter += 1
                
                # Generate constraint
                if not self._generate_constraint(tmp_file, strategies[strategy], cnfratio, cntsize, final_logic_to_use):
                    continue
                    
                # Test and mutate
                self._test_and_mutate(tmp_file, final_logic_to_use, strategies[strategy])
                
            except Exception as ee:
                print(f"Error in gen_and_mut: {ee}")
    
    def gen_and_meta(self, idt):
        """Generate and perform meta-testing"""
        counter = 0
        
        while True:
            try:
                # Similar to gen_and_mut but for meta-testing
                if counter % self.args.count == 0:
                    cnfratio = random.randint(2, 50)
                    cntsize = random.randint(25, 550)
                    strategy = random.randint(0, len(strategies) - 1)
                    
                    logiclist = self._get_logic_list()
                    logic = random.randint(0, len(logiclist) - 1)
                    counter = 0
                    
                final_logic_to_use = logiclist[logic]
                
                if self.args.logicmode in all_logic_options:
                    final_logic_to_use = self.args.logicmode
                    
                name = f'meta_input-{idt}_{counter}_{strategies[strategy]}_{cnfratio}_{cntsize}_{final_logic_to_use}.smt2'
                tmp_file = os.path.join(self.args.output, 'input', name)
                
                counter += 1
                
                # Generate and test with multiple solvers
                if self._generate_constraint(tmp_file, strategies[strategy], cnfratio, cntsize, final_logic_to_use):
                    self._meta_test(tmp_file)
                    
            except Exception as ee:
                print(f"Error in gen_and_meta: {ee}")
    
    def _get_logic_list(self):
        """Get logic list based on logic mode"""
        logic_map = {
            'bv': bv_logic_options,
            'int': int_logic_options,
            'real': real_logic_options,
            'bool': bool_logic_options,
            'str': ['QF_S', 'QF_SLIA', 'QF_SNIA'],
            'qu': q_logic_options,
            'qf': qf_logic_options,
            'new': ira_logics,
            'uf': uf_logic_options,
            'qfla': qfla_logics,
            'la': la_logics
        }
        
        return logic_map.get(self.args.logicmode, qf_logic_options)
    
    def _get_logic_list_qf(self):
        """Get quantifier-free logic list based on logic mode"""
        logic_map = {
            'bv': qf_bv_logic_options,
            'int': qf_int_logic_options,
            'real': qf_real_logic_options
        }
        
        return logic_map.get(self.args.logicmode, qf_logic_options)
    
    def _generate_constraint(self, tmp_file, strategy, cnfratio, cntsize, logic):
        """Generate SMT constraint using the generator"""
        cmd = ['python3', self.generator, '--strategy', str(strategy), '--cnfratio', str(cnfratio),
               '--cntsize', str(cntsize), '--logic', str(logic), '--difftest', '1']
        
        if self.args.solvermode == "unsat_core":
            cmd.extend(['--difftestcore', '1'])
        elif self.args.solvermode == "proof":
            cmd.extend(['--proof', '1'])
            
        logging.debug("Enter constraint generation")
        logging.debug(cmd)
        
        p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        is_timeout_gene = [False]
        timer_gene = Timer(15, self.terminate_process, args=[p_gene, is_timeout_gene])
        timer_gene.start()
        
        try:
            out_gene = p_gene.stdout.readlines()
            out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
            
            with open(tmp_file, 'w') as f:
                f.write(out_gene)
                
            if os.stat(tmp_file).st_size == 0:
                print("seed file empty")
                return False
                
        finally:
            p_gene.stdout.close()
            timer_gene.cancel()
            
        return True
    
    def _test_and_mutate(self, tmp_file, logic, strategy):
        """Test seed file and perform mutations"""
        # Setup solver command
        cmd_tool = self._setup_solver_command()
        if not cmd_tool:
            return
            
        # Configure solver options based on logic and strategy
        self._configure_solver_options(cmd_tool, logic, strategy)
        
        # Test seed file
        if not self._test_seed_file(tmp_file, cmd_tool):
            if os.path.isfile(tmp_file):
                os.remove(tmp_file)
            return
            
        # Perform mutations
        self._perform_mutations(tmp_file, cmd_tool)
    
    def _setup_solver_command(self):
        """Setup solver command"""
        solver_map = {
            'yices': self.get_smt_solver_path("yices"),
            'cvc5': self.get_smt_solver_path("cvc5"),
            'z3': self.get_smt_solver_path("z3"),
            'open': self.get_smt_solver_path("open"),
            'pol': self.get_smt_solver_path("pol")
        }
        
        to_test = solver_map.get(self.args.solver, self.get_smt_solver_path("z3"))
        return to_test.split(' ')
    
    def _configure_solver_options(self, cmd_tool, logic, strategy):
        """Configure solver-specific options"""
        if 'cvc' in ' '.join(cmd_tool):
            cmd_tool.append('--quiet')
            
            if str(logic) in ['QF_S', 'SEQ', 'QF_SLIA', 'QF_SNIA', 'QF_UFSLIA']:
                cmd_tool.append('--strings-exp')
            elif str(logic) == 'SET':
                cmd_tool.append('--sets-ext')
                
            if str(strategy) != 'noinc':
                cmd_tool.append('--incremental')
            cmd_tool.append('--check-models')
            
        elif any(solver in ' '.join(cmd_tool) for solver in ['yice', 'boolec']):
            if str(strategy) != 'noinc':
                cmd_tool.append('--incremental')
    
    def _test_seed_file(self, tmp_file, cmd_tool):
        """Test the generated seed file"""
        cmd_seed = cmd_tool + [tmp_file]
        logging.debug("Seed res: ")
        logging.debug(cmd_seed)
        
        env = os.environ.copy()
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
            elif any(keyword in out_seed for keyword in ["unknown logic", "error"]):
                return False
            elif any(keyword in out_seed for keyword in ["Santi", 'ASSERTION', 'Assert', 'Fat']):
                if self._check_error_against_blacklist(out_seed):
                    print("find error in seed!")
                    print("seed cmd: ", cmd_seed)
                    print("seed res: ", out_seed)
                    crash_file = os.path.join(self.args.output, 'crash', os.path.basename(tmp_file))
                    shutil.copy(tmp_file, crash_file)
                    return False
                    
        finally:
            ptool.stdout.close()
            timertool.cancel()
            
        return True
    
    def _perform_mutations(self, tmp_file, cmd_tool):
        """Perform mutations on the seed file"""
        counter = hashlib.md5(tmp_file.encode('utf-8')).hexdigest()
        cmd_ori = cmd_tool[:-1]  # Remove file argument
        
        name_base = f'muta_input-0_{counter[:6]}_'
        gene = StringMutation(tmp_file)
        
        # Configure mutation based on solver mode
        if self.args.solvermode == 'unsat_core':
            gene.enable_unsat_core()
        elif self.args.solvermode == 'proof':
            gene.enable_proof()
        elif self.args.solvermode == 'smtopt':
            gene.enable_smtopt()
            
        for i in range(self.args.count):
            tmp_file_mut = os.path.join(self.args.output, 'input', f"{name_base}{i}.smt2")
            
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
                
            # Test the mutation
            if self._test_mutation(tmp_file_mut, cmd_ori):
                break  # Found an error
    
    def _test_mutation(self, tmp_file_mut, cmd_mut):
        """Test a single mutation"""
        cmd_mut_full = cmd_mut + [tmp_file_mut]
        logging.debug(cmd_mut_full)
        
        env = os.environ.copy()
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
            
            if any(keyword in out_mut for keyword in ["Santi", 'ASSERTION', 'Assert', 'Fat']):
                if self._check_error_against_blacklist(out_mut):
                    print("find error in mutation!")
                    print("mut cmd: ", cmd_mut_full)
                    print("mut res: ", out_mut)
                    crash_file = os.path.join(self.args.output, 'crash', os.path.basename(tmp_file_mut))
                    shutil.copy(tmp_file_mut, crash_file)
                    return True
            else:
                if os.path.isfile(tmp_file_mut):
                    os.remove(tmp_file_mut)
                    
        finally:
            pmut.stdout.close()
            timermut.cancel()
            
        return False
    
    def _meta_test(self, tmp_file):
        """Perform meta-testing with multiple solvers"""
        m_tools = [
            self.get_smt_solver_path("z3"),
            self.get_smt_solver_path("cvc5")
        ]
        
        if self.args.config != 'no':
            config = configparser.ConfigParser()
            config.read(self.args.config)
            m_tools = list(config['DIFFSOLVERS'].values())
            
        results = []
        for tool in m_tools:
            result = self._test_with_solver(tmp_file, tool.split(' '))
            results.append(result)
            
        # Check for inconsistencies
        if len(set(results)) > 1:
            print("find inconsistency in meta-testing!")
            print(tmp_file)
            crash_file = os.path.join(self.args.output, 'crash', os.path.basename(tmp_file))
            shutil.copy(tmp_file, crash_file)
    
    def _test_with_solver(self, tmp_file, cmd_tool):
        """Test file with a specific solver"""
        cmd = cmd_tool + [tmp_file]
        
        env = os.environ.copy()
        env["ASAN_OPTIONS"] = "log_path=stdout:" + env.get("ASAN_OPTIONS", "")
        env["ASAN_OPTIONS"] += "detect_leaks=0"
        
        try:
            p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
            is_timeout = [False]
            timer = Timer(10, self.terminate_process, args=[p, is_timeout])
            timer.start()
            
            out = p.stdout.readlines()
            out = ' '.join([str(element.decode('UTF-8')) for element in out])
            
            if is_timeout[0]:
                return "timeout"
            elif "sat" in out:
                return "sat"
            elif "unsat" in out:
                return "unsat"
            else:
                return "unknown"
                
        finally:
            p.stdout.close()
            timer.cancel()
    
    def _check_error_against_blacklist(self, output):
        """Check if error should be reported based on blacklist"""
        for item in self.black_list:
            if item and item in output:
                return False
        return True
    
    def run(self):
        """Main run method for generation-based fuzzing"""
        parser = self.setup_args()
        args = parser.parse_args()
        
        self.initialize(args)
        
        # Setup output directory
        crashes, inputs = self.setup_output_directory(args.output)
        
        # Check if maxsmt mode
        if args.solvermode == "maxsmt":
            self.m_test_maxsmt = True
            
        try:
            # Start generation and mutation workers
            tasks = list(range(args.workers))
            
            if args.config != 'no':  # Meta-testing mode
                self.pool.map(self.gen_and_meta, tasks)
            else:  # Regular generation mode
                self.pool.map(self.gen_and_mut, tasks)
                
        finally:
            self.cleanup()
            print("We finish here, have a good day!")


def main():
    """Main entry point for generation runner"""
    runner = GenRunner()
    runner.run()


if __name__ == "__main__":
    main() 