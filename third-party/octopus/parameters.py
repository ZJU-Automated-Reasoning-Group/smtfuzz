from termcolor import colored


def get_supported_theories(solver):
    theories = {
        "z3": ["ABV", "ALIA", "AUFNIA", "AUFBV", "LRA", "QF_ALIA", "QF_AUFNIA", "QF_LRA", "QF_RDL", "QF_UFIDL",
               "QF_UFNRA", "UFDTLIA", "AUFDTLIA", "AUFNIRA", "NIA", "QF_ANIA", "QF_AX", "QF_FP", "QF_NIA",
               "QF_UFLIA", "UFLIA", "AUFLIA", "BV", "NRA", "QF_AUFBV", "QF_BV", "QF_IDL", "QF_SLIA", "QF_NIRA",
               "QF_UF", "QF_UFLRA", "UF", "UFLRA", "AUFLIRA", "LIA", "QF_ABV", "QF_AUFLIA", "QF_BVFP",
               "QF_LIA", "QF_NRA", "QF_UFBV", "QF_UFNIA", "UFDT", "UFNIA", "QF_S", "QF_FPLRA", "QF_LIRA", "UFIDL",
               "UFBV"],

        "yices": ["QF_ABV", "QF_ALIA", "QF_AUFBV", "QF_AUFLIA", "QF_AX", "QF_BV", "QF_IDL", "QF_LIA", "QF_LIRA",
                  "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA", "QF_RDL", "QF_UF", "QF_UFBV", "QF_UFIDL", "QF_UFLIA",
                  "QF_UFLRA", "QF_UFNIA", "QF_UFNIRA", "QF_UFNRA", "LRA",
                  "UFLRA"],

        "z3str3": ["QF_S"],

        "smtinterpol": ["QF_ABV", "QF_ALIA", "QF_AUFBV", "QF_AUFLIA", "QF_AX", "QF_BV", "QF_IDL", "QF_LIA", "QF_LIRA",
                        "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA", "QF_RDL", "QF_UF", "QF_UFBV", "QF_UFIDL", "QF_UFLIA",
                        "QF_UFLRA", "QF_UFNIA", "QF_UFNIRA", "QF_UFNRA", "LRA",
                        "UFLRA"],

        "cvc4": ["ALIA", "AUFNIA", "LRA", "QF_ALIA", "QF_AUFNIA", "QF_LRA", "QF_RDL", "QF_UFIDL",
                 "QF_UFNRA", "UFDTLIA", "AUFDTLIA", "AUFNIRA", "NIA", "QF_ANIA", "QF_AX", "QF_FP", "QF_NIA",
                 "QF_UFLIA", "UFLIA", "AUFLIA", "BV", "NRA", "QF_AUFBV", "QF_BV", "QF_IDL", "QF_NIRA",
                 "QF_UF", "QF_UFLRA", "UF", "UFLRA", "AUFLIRA", "LIA", "QF_ABV", "QF_AUFLIA", "QF_BVFP",
                 "QF_LIA", "QF_NRA", "QF_UFBV", "QF_UFNIA", "UFDT", "UFNIA", "QF_S"],

        "mathsat": ["QF_ABV", "QF_ABVFP", "QF_ABVFPLRA", "QF_ALIA", "QF_ANIA", "QF_AUFBV", "QF_AUFLIA",
                    "QF_AUFNIA", "QF_AX", "QF_BV", "QF_BVFP", "QF_BVFPLRA", "QF_FP", "QF_FPLRA", "QF_IDL",
                    "QF_LIA", "QF_LIRA", "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA", "QF_RDL", "QF_UF", "QF_UFBV",
                    "QF_UFFP", "QF_UFIDL", "QF_UFLIA", "QF_UFLRA", "QF_UFNIA", "QF_UFNRA"],

        "bitwuzla": ["BV", "QF_ABV", "QF_ABVFP", "QF_AUFBV", "QF_BV", "QF_BVFP", "QF_FP", "QF_UFBV", "QF_UFFP"]

    }
    return theories[solver]


def tactic_choice():
    tactic = ["sat", "smt", "ctx-solver-simplify", "unit-subsume-simplify", "aig", "purify-arith", "fm",
                            "blast-term-ite", "ctx-simplify", "der", "elim-term-ite", "elim-uncnstr", "pb-preprocess",
                            "reduce-args", "nlsat", "nlqsat", "qe-light", "qe", "qsat", "qe2",
                            "simplify", "elim-and", "symmetry-reduce", "default", "cofactor-term-ite",
                            "special-relations", "fix-dl-var", "factor", "distribute-forall",
                            "solve-eqs", "dom-simplify", "sat-preprocess", "degree-shift", "injectivity", "snf", "nnf",
                            "occf", "sat-preprocess", "subpaving", "bit-blast", "propagate-values",
                            "reduce-invertible", "split-clause"]
    return tactic


parameters = {
    "max_depth": 20,
    "max_assert": 20,
    "enrichment_steps": 1000,
    "number_of_mutants": 1000,
    "mutant_generation_timeout": 60,  # 15 mins
    "mutant_running_timeout": 1800,  # 15 mins
    "solver_timeout": 10,
    "check_sat_using": ["yes", "no"],
    # remove an option if you want a single mode. Otherwise octopus will choose with a prob
    "incremental": ["yes", "no"]
    # remove an option if you want a single mode. Otherwise octopus will choose with a prob
}


def get_parameters_dict(replication_mode):
    if not replication_mode:
        print("#######" + colored(" Getting the normal fuzzing parameters", "magenta", attrs=["bold"]))
        print(str(parameters))
        return parameters
    else:
        print("We don not support that.")
