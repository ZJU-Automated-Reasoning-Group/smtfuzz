class MainArgumentParser(object):

    def __init__(self):
        self.parsed_arguments = dict()
        self.solverbin = None
        self.solver = None
        self.seeds = None
        self.timeout = None
        self.mode = None
        self.cores = None
        self.reduce = None
        self.bugfile = None
        self.priorfile = None
        self.bugtype = None
        self.bugdir = None

    def parse_arguments(self, parser):
        parser.add_argument("--solverbin", help="path to the first solver bin.\n"
                                                "Note that: if only one solver provided, soundness bugs will be missed. "
                                                "Only invalid model bugs and crashes can be found.")
        parser.add_argument("--solver", help="the first solver name e.g. z3, cvc5.\n"
                                             "Note that: if only one solver provided, soundness bugs will be missed. "
                                             "Only invalid model bugs and crashes can be found.")

        parser.add_argument("--seeds", help="path to the seeds directory.")
        parser.add_argument("--timeout", help="timeout for solving each SMT2 file.")
        parser.add_argument("--mode", help="mode of the tool to identify the type of the bug. [soundness, all].")
        parser.add_argument("--cores", help="number of cores to use for parallel execution.")
        parser.add_argument("--reduce", nargs='?', const=True, default=False,
                            help="use the reduction strategy to reduce the SMT2 file size.")
        parser.add_argument("--bugfile", help="path to the bug file.")
        parser.add_argument("--priorfile", help="path to the prior file.")
        parser.add_argument("--bugtype", help="type of the bug to find. [soundness, completeness, performance].")
        parser.add_argument("--bugdir", help="path to the bug directory.")

        arguments = vars(parser.parse_args())

        self.solverbin = arguments["solverbin"]
        self.solver = arguments["solver"]
        self.seeds = arguments["seeds"]
        self.timeout = arguments["timeout"] if arguments["timeout"] else 10
        self.mode = arguments["mode"] if arguments["mode"] else "all"
        self.cores = arguments["cores"] if arguments["cores"] else 1
        self.reduce = arguments["reduce"]
        self.bugfile = arguments["bugfile"]
        self.priorfile = arguments["priorfile"]
        self.bugtype = arguments["bugtype"]
        self.bugdir = arguments["bugdir"]

    def get_arguments(self):
        self.parsed_arguments["solverbin"] = self.solverbin
        self.parsed_arguments["solver"] = self.solver
        self.parsed_arguments["timeout"] = self.timeout
        self.parsed_arguments["mode"] = self.mode
        self.parsed_arguments["seeds"] = self.seeds
        self.parsed_arguments["cores"] = self.cores
        self.parsed_arguments["reduce"] = self.reduce
        self.parsed_arguments["bugfile"] = self.bugfile
        self.parsed_arguments["priorfile"] = self.priorfile
        self.parsed_arguments["bugtype"] = self.bugtype
        self.parsed_arguments["bugdir"] = self.bugdir

        return self.parsed_arguments
