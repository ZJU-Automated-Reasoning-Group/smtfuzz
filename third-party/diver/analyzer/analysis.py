import inspect
from parser.smt_parser import *
from analyzer.spc_analyzer import *


def get_logic(logic):
    logic_ = 0
    if "ALL" == logic:
        logic_ = (logic_ | 127)
    if "S" in logic:
        logic_ = (logic_ | 4)
    if "I" in logic:
        logic_ = (logic_ | 2)
    if "R" in logic:
        logic_ = (logic_ | 1)
    return logic_


def preprocess(formula, v_type, model, logic):
    C = {}
    try:
        ast = transform_smt_to_ast(formula)
        analyzer = ConstraintAnalyzer(ast, v_type, model, get_logic(logic))
        analyzer.generateSPC()
        C["var"] = analyzer.var
        C["const"] = analyzer.const
        C["spc"] = analyzer.C
        C["term"] = analyzer.terms
        C["ast"] = ast
        C["parent"] = analyzer.parent
        C["cal"] = analyzer.E
        C["tree"] = analyzer.tree
        return C
    except Exception as e:
        trace = inspect.trace()
        fn = trace[-1].filename
        lineno = trace[-1].lineno
        print("Runtime error at %s:%s" % (fn, lineno), flush=True)
        print("msg: " + str(e), flush=True)
        return None
