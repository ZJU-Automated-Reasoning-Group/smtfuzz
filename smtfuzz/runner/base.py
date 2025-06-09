"""Base runner class with common functionality for SMT fuzzing"""

import argparse
import hashlib
import json
import logging
import os
import signal
import subprocess
import sys
import time
from threading import Timer
from multiprocessing.pool import ThreadPool
import shutil


class Statistic:
    """Statistics tracking for fuzzing operations"""
    
    def __init__(self):
        print("Sparrow is running:")
        self.starttime = time.time()
        self.seeds = 0
        self.mutants = 0
        self.error = 0
        self.soundness = 0
        self.timeout = 0
        self.solving_time = 0
        self.mutation_time = 0
        self.ignored = 0
        self.profile_data = []

    def printbar(self):
        bar = "[time:%ds, #mutant:%d, #seed:%d, #crash:%d, #unsound:%d, #timeout:%d, #ignored:%d]" \
              % (time.time() - self.starttime, self.mutants, self.seeds, self.error, self.soundness, self.timeout,
                 self.ignored)
        print(bar, end="\r", flush=True)

    def printsum(self):
        summary = """

Summary:
Passed time: %ds
Generated mutants: %d
Used seeds: %d
Crash issues: %d
Unsound issues: %d
Timeout cases: %d
Ignored issues: %d
""" \
                  % (time.time() - self.starttime, self.mutants, self.seeds, self.error, self.soundness, self.timeout,
                     self.ignored)
        print(summary, end="\n", flush=True)


class BaseRunner:
    """Base class for SMT fuzzing runners"""
    
    def __init__(self):
        self.config = None
        self.black_list = []
        self.statistic = None
        self.pool = None
        self.args = None
        
    def load_config(self, config_path='test_config.json'):
        """Load configuration from JSON file"""
        try:
            with open(config_path, 'r') as file:
                self.config = json.load(file)
        except FileNotFoundError:
            logging.warning(f"Config file {config_path} not found, using defaults")
            self.config = {}
    
    def get_smt_solver_path(self, solver: str):
        """Get solver path from configuration"""
        return self.config.get(solver, solver)
    
    def load_black_list(self, black_list_files=None):
        """Load black list from files"""
        if black_list_files is None:
            black_list_files = ['../black_list_cvc4_new', '../black_list_z3', 
                              '../black_list_open', '../black_list_yices2']
        
        self.black_list = []
        for f in black_list_files:
            try:
                with open(f, 'r') as bf:
                    for line in bf:
                        self.black_list.append(line.replace("\n", ""))
            except FileNotFoundError:
                logging.warning(f"Black list file {f} not found")
    
    def setup_output_directory(self, out_dir):
        """Setup output directory structure"""
        if os.path.exists(out_dir):
            shutil.rmtree(out_dir)
        os.makedirs(out_dir)
        
        crashes = os.path.join(out_dir, 'crash')
        inputs = os.path.join(out_dir, 'input')
        os.makedirs(crashes)
        os.makedirs(inputs)
        
        return crashes, inputs
    
    def terminate_process(self, process, is_timeout):
        """Terminate a subprocess with timeout handling"""
        if process.poll() is None:
            try:
                process.terminate()
                is_timeout[0] = True
            except Exception as e:
                logging.error(f"Error terminating process: {e}")
    
    def try_z3_mutate(self, file, output, bet_mutator_path):
        """Try Z3-based mutation"""
        try:
            from smtfuzz.bet.bet_mutator import Z3Mutation
        except ImportError:
            return False
            
        ret = True
        cmd = ['python3', bet_mutator_path, "--input", file, "--output", output]
        
        if hasattr(self.args, 'optfuzz') and self.args.optfuzz == "yes":
            if hasattr(self.args, 'solver'):
                if self.args.solver == "z3":
                    cmd.extend(["--optionmode", "z3"])
                elif self.args.solver == "cvc5":
                    cmd.extend(["--optionmode", "cvc4"])

        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        is_timeout = [False]
        timer = Timer(5, self.terminate_process, args=[p, is_timeout])
        timer.start()
        
        try:
            out = p.stdout.readlines()
            out = ' '.join([str(element.decode('UTF-8')) for element in out])
            
            if is_timeout[0]:
                logging.debug("Timeout when using z3py for mutation")
                ret = False
            elif any(keyword in out for keyword in ["error", "Segment", "Exception"]):
                logging.debug("Error when using z3py for mutation!")
                logging.debug(out)
                ret = False
        finally:
            p.stdout.close()
            timer.cancel()
            
        return ret
    
    def setup_common_args(self, parser):
        """Setup common command line arguments"""
        parser.add_argument('--input', dest='input', type=str, help="Input directory or file")
        parser.add_argument('--output', dest='output', default='~/tmp/res/', type=str, help="Output directory")
        parser.add_argument('--timeout', dest='timeout', default=10, type=int, help="Timeout for each solving")
        parser.add_argument('--count', dest='count', default=50, type=int, help="Counts for each combination")
        parser.add_argument('--workers', dest='workers', default=1, type=int, help="Number of threads")
        parser.add_argument('--solvermode', dest='solvermode', default='default', type=str, help="Solver mode")
        parser.add_argument('--logicmode', dest='logicmode', default='default', type=str, help="Logic mode")
        parser.add_argument('--config', dest='config', default='no', type=str, help="Configuration file")
        parser.add_argument('--solver', dest='solver', default='all', type=str, help="Target solver")
        parser.add_argument('--optfuzz', dest='optfuzz', default='no', type=str, help="Enable option fuzzing")
        parser.add_argument("-v", "--verbose", help="Increase output verbosity", action="store_true")
        parser.add_argument("-p", "--profile", help="Profile the speed of mutation", action="store_true")
        
    def setup_signal_handlers(self):
        """Setup signal handlers for graceful shutdown"""
        def signal_handler(sig, frame):
            if self.pool:
                self.pool.terminate()
            if self.statistic:
                self.statistic.printsum()
                if len(self.statistic.profile_data) > 0:
                    import statistics as st
                    print("Min: ", min(self.statistic.profile_data))
                    print("Max: ", max(self.statistic.profile_data))
                    print("Avg: ", sum(self.statistic.profile_data) / len(self.statistic.profile_data))
                    print("Std: ", st.pstdev(self.statistic.profile_data))
            
            # Cleanup processes
            for proc in ['python3', 'python3.7', 'python3.8', 'z3', 'cvc5', 'yices_smt2', 'opensmt', 'boolector']:
                os.system(f'pkill -9 {proc}')
            
            print("We finish here, have a good day!")
            sys.exit(0)
        
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        signal.signal(signal.SIGQUIT, signal_handler)
        signal.signal(signal.SIGHUP, signal_handler)
    
    def initialize(self, args):
        """Initialize the runner with arguments"""
        self.args = args
        
        if args.verbose:
            logging.basicConfig(level=logging.DEBUG)
        
        self.load_config()
        self.load_black_list()
        self.setup_signal_handlers()
        
        if args.workers == 1:
            self.statistic = Statistic()
        
        self.pool = ThreadPool(processes=args.workers)
    
    def run(self):
        """Main run method - to be implemented by subclasses"""
        raise NotImplementedError("Subclasses must implement run method")
    
    def cleanup(self):
        """Cleanup resources"""
        if self.pool:
            self.pool.close()
            self.pool.join()
        
        if self.statistic:
            self.statistic.printsum()
            if len(self.statistic.profile_data) > 0:
                import statistics as st
                print("Min: ", min(self.statistic.profile_data))
                print("Max: ", max(self.statistic.profile_data))
                print("Avg: ", sum(self.statistic.profile_data) / len(self.statistic.profile_data))
                print("Std: ", st.pstdev(self.statistic.profile_data)) 