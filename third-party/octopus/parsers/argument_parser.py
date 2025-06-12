
import time

class MainArgumentParser(object):

    def __init__(self):
        self.parsed_arguments = dict()
        self.core = None
        self.cores = None
        self.server = None
        self.seed = None
        self.benchmark = None
        self.theory = None
        self.solverbin = None
        self.solver = None
        self.file_path = None
        self.check_sat_using = None
        self.incremental = None
        self.start_file = 0
        self.testfile_num = 0
        self.file_one_core = 0
        self.assignments = 10
        self.generation = None


    def parse_arguments(self, parser):
        parser.add_argument("--core", help="core to run on")
        parser.add_argument("--cores", help="number of cores to run on")
        parser.add_argument("--server", help="server")
        parser.add_argument("--seed", help="seed for randomness")
        parser.add_argument("--benchmark", help="Path to benchmark folder")
        parser.add_argument("--theory", help="Theory")
        parser.add_argument("--solverbin", help="path to solver bin")
        parser.add_argument("--solver", help="solver name e.g. z3, cvc5")
        parser.add_argument("--file_path", help="path to a SMT file")
        parser.add_argument("--check_sat_using", help="check_sat_using (only for minimizer)")
        parser.add_argument("--incremental", nargs='?', const=True, default=False, help="incremental")
        parser.add_argument("--start_file", help="The first file number")
        parser.add_argument("--testfile_num", help="Number of test files")
        parser.add_argument("--file_one_core", help="Number of files tested on a core")
        parser.add_argument("--assignments", help="Number of assignments")
        parser.add_argument("--generation", nargs='?', const=True, default=False, help="formula snippet generation")

        arguments = vars(parser.parse_args())

        SEED = arguments["seed"]
        if SEED is None:
            SEED = str(int(time.time()))
            print("####### [NO SEED PROVIDED] - Using Unix time as seed: ", end="")
            print(SEED)
        else:
            print("####### Provided Seed: " + str(SEED))

        self.core = arguments["core"] if arguments["core"] is not None else "0"
        self.cores = arguments["cores"] if arguments["cores"] is not None else None
        self.server = arguments["server"] if arguments["server"] is not None else "local"
        self.seed = SEED
        self.benchmark = arguments["benchmark"]
        self.theory = arguments["theory"]
        self.solverbin = arguments["solverbin"]
        self.solver = arguments["solver"]
        self.file_path = arguments["file_path"]
        self.check_sat_using = arguments["check_sat_using"]
        self.incremental = arguments["incremental"]
        self.start_file = arguments["start_file"] if arguments["start_file"] is not None else 0
        self.testfile_num = arguments["testfile_num"] if arguments["testfile_num"] is not None else 0
        self.file_one_core = arguments["file_one_core"] if arguments["file_one_core"] is not None else 0
        self.assignments = arguments["assignments"] if arguments["assignments"] is not None else 10
        self.generation = arguments["generation"]

    def get_arguments(self):
        self.parsed_arguments["core"] = self.core
        self.parsed_arguments["cores"] = self.cores
        self.parsed_arguments["server"] = self.server
        self.parsed_arguments["seed"] = self.seed
        self.parsed_arguments["benchmark"] = self.benchmark
        self.parsed_arguments["theory"] = self.theory
        self.parsed_arguments["solverbin"] = self.solverbin
        self.parsed_arguments["solver"] = self.solver
        self.parsed_arguments["file_path"] = self.file_path
        self.parsed_arguments["check_sat_using"] = self.check_sat_using
        self.parsed_arguments["incremental"] = self.incremental
        self.parsed_arguments["start_file"] = self.start_file
        self.parsed_arguments["testfile_num"] = self.testfile_num
        self.parsed_arguments["file_one_core"] = self.file_one_core
        self.parsed_arguments["assignments"] = self.assignments
        self.parsed_arguments["generation"] = self.generation
        return self.parsed_arguments
