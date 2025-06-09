import argparse
import time


class ArgParser(object):

    def __init__(self):
        self.parsed_arg = dict()
        self.solver_api = None
        self.solver = None
        self.solverbin = None
        self.timeout = None
        self.option = None

        self.benchmark = None
        self.logic = None
        self.opt = None

        self.seed = None
        self.max_depth = None
        self.mutants = None

        self.cores = 1
        self.experiment = "0"
        self.mode = "diver"
        self.debug = True

    def parse_arguments(self, parser):
        parser.add_argument('-a', "--solverapi", default=None, help="Target API SMT Solver e.g., cvc, z3")
        parser.add_argument('-s', "--solver", help="Testing Target SMT Solver e.g., dreal, cvc, z3")
        parser.add_argument('-b', "--solverbin", help="Path to SMT Solver Binary")
        parser.add_argument('-t', "--timeout", default=10, help="Timeout of Invoking SMT Solver (default = 10s)")
        parser.add_argument('-o', "--option", default=None,
                            help="Option for Testing SMT Solver, e.g., option1,option2,...")

        parser.add_argument('-i', "--benchmark", help="Path to Seed Formulas")
        parser.add_argument('-l', "--logic", help="Logic of Seed Formulas, e.g., QF_NRA, QF_SLIA,...")
        parser.add_argument("--opt", default="True", help="Pre-Process for Seed Formula (default = True)")

        parser.add_argument("--seed", help="Seed for Randomness")
        parser.add_argument("--max_depth", default=5, help="Max Depth for Generation Step (default = 5)")
        parser.add_argument('-m', "--mutants", default=1000,
                            help="Number of Mutants generated per seed (default = 1000)")

        parser.add_argument("--cores", default=1, help="Number of Cores (default = 1)")
        parser.add_argument("--experiment", default="0", help="Exeriment Number (default = None)")
        parser.add_argument("--mode", default="diver", help="the variant of Diver (e.g., diver, nocomp, noweight)")
        parser.add_argument("--debug", default="true", help="Debugging option for obtaining bug informations")
        arguments = vars(parser.parse_args())

        SEED = arguments["seed"]
        if SEED is None:
            SEED = str(int(time.time()))

        if arguments["solverapi"] is None:
            self.solver_api = arguments["solver"]
        else:
            self.solver_api = arguments["solverapi"]
        self.solver = arguments["solver"]
        self.solverbin = arguments["solverbin"]
        self.timeout = arguments["timeout"]
        if arguments["option"] is None:
            self.option = []
        else:
            self.option = arguments["option"].split(',')

        self.benchmark = arguments["benchmark"]
        self.logic = arguments["logic"]
        self.opt = arguments["opt"]

        self.seed = SEED
        self.max_depth = arguments["max_depth"]
        self.mutants = arguments["mutants"]

        self.cores = arguments["cores"]
        self.experiment = arguments["experiment"]
        self.mode = arguments["mode"]
        self.debug = (arguments["debug"] == "true")

    def get_arguments(self):
        self.parsed_arg["solver_api"] = self.solver_api
        self.parsed_arg["solverbin"] = self.solverbin
        self.parsed_arg["solver"] = self.solver
        self.parsed_arg["option"] = self.option
        self.parsed_arg["benchmark"] = self.benchmark
        self.parsed_arg["seed"] = self.seed
        self.parsed_arg["max_depth"] = int(self.max_depth)
        self.parsed_arg["timeout"] = self.timeout
        self.parsed_arg["logic"] = self.logic
        self.parsed_arg["server"] = "local"
        self.parsed_arg["mutants"] = int(self.mutants)
        self.parsed_arg["opt"] = (self.opt == "True")
        self.parsed_arg["cores"] = self.cores
        self.parsed_arg["mode"] = self.mode
        self.parsed_arg["experiment"] = self.experiment
        self.parsed_arg["debug"] = self.debug
        return self.parsed_arg
