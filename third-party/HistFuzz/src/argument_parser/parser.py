"""
MIT License

Copyright (c) 2023 The histfuzz authors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""


import time


class MainArgumentParser(object):

    def __init__(self):
        self.parsed_arguments = dict()
        self.core = None
        self.cores = None
        self.solverbin1 = None
        self.solverbin2 = None
        self.solver1 = None
        self.solver2 = None
        self.incremental = None
        self.update = None
        self.token = None
        self.conf = None
        self.sup = None
        self.option = None
        self.mutant = None
        self.bugfolder = None
        self.c1 = None


    def parse_arguments(self, parser):
        parser.add_argument("--update", nargs='?', const=True, default=False,
                            help="update historical data.\nYou should use `--token` to add your GitHub token")
        parser.add_argument("--token",
                            help="Your github token. You should input your github token for updating historical data")
        parser.add_argument("--core", help="core to run on")
        parser.add_argument("--cores", help="number of cores to run on")
        parser.add_argument("--solverbin1", help="path to the first solver bin.\n"
                                                 "Note that: if only one solver provided, soundness bugs will be missed. "
                                                 "Only invalid model bugs and crashes can be found.")
        parser.add_argument("--solver1", help="the first solver name e.g. z3, cvc5.\n"
                                              "Note that: if only one solver provided, soundness bugs will be missed. "
                                              "Only invalid model bugs and crashes can be found.")
        parser.add_argument("--solverbin2", help="path to the second solver bin")
        parser.add_argument("--solver2", help=" the second solver name e.g. z3, cvc5")
        parser.add_argument("--incremental", nargs='?', const=True, default=False, help="incremental")
        parser.add_argument("--c1", nargs='?', const=True, default=False, help="Employ the resource files for replicate evaluation C-1")
        parser.add_argument("--conf", help=" the min Confidence for association analysis")
        parser.add_argument("--sup", help=" the min Support for association analysis. Here, we use the number of "
                                          "occurrences of atomic formulas as Support.")
        parser.add_argument("--mutant", help=" the number of mutants generated totally")
        parser.add_argument("--bugfolder", "-b", help=" the folder containing bug-triggering inputs collect from "
                                                      "solvers' bug trackers")
        parser.add_argument("--option", type=str, choices=["default", "regular", "comprehensive"],
                            help=" the tested options of Z3 and cvc5. \n"
                                 "default: the default mode of solvers \n"
                                 "regular: some common options \n "
                                 "comprehensive: almost all the options (enable with caution)")
        arguments = vars(parser.parse_args())

        self.core = arguments["core"] if arguments["core"] is not None else "0"
        self.cores = arguments["cores"] if arguments["cores"] is not None else "1"
        self.solverbin1 = arguments["solverbin1"] if not arguments["update"] else None
        self.solverbin2 = arguments["solverbin2"] if not arguments["update"] else None
        self.solver1 = arguments["solver1"] if not arguments["update"] else None
        self.solver2 = arguments["solver2"] if not arguments["update"] else None
        self.incremental = "random" if arguments["incremental"] else "non-incremental"
        self.bugfolder = arguments["bugfolder"]
        self.update = arguments["update"]
        self.token = arguments["token"]
        self.mutant = arguments["mutant"]
        self.c1 = arguments["c1"]
        self.conf = float(arguments["conf"]) if arguments["conf"] is not None else 0.5
        self.sup = float(arguments["sup"]) if arguments["sup"] is not None else 9
        self.option = arguments["option"] if arguments["option"] is not None else "default"

    def get_arguments(self):
        self.parsed_arguments["core"] = self.core
        self.parsed_arguments["cores"] = self.cores
        self.parsed_arguments["solverbin1"] = self.solverbin1
        self.parsed_arguments["solverbin2"] = self.solverbin2
        self.parsed_arguments["solver1"] = self.solver1
        self.parsed_arguments["solver2"] = self.solver2
        self.parsed_arguments["incremental"] = self.incremental
        self.parsed_arguments["update"] = self.update
        self.parsed_arguments["token"] = self.token
        self.parsed_arguments["conf"] = self.conf
        self.parsed_arguments["sup"] = self.sup
        self.parsed_arguments["mutant"] = self.mutant
        self.parsed_arguments["option"] = self.option
        self.parsed_arguments["bugfolder"] = self.bugfolder
        self.parsed_arguments["c1"] = self.c1

        return self.parsed_arguments
