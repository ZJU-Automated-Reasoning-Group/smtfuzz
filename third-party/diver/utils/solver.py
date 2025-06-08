import subprocess
import os,sys
from interval import interval, inf, imath
from fractions import *
from decimal import *
from utils.cvc5Interface import *
import re
import cvc5
from cvc5 import Kind
from z3 import *


crash_list = [
    "Exception",
    "lang.AssertionError",
    "lang.Error",
    "runtime error",
    "LEAKED",
    "Leaked",
    "Segmentation fault",
    "segmentation fault",
    "segfault",
    "ASSERTION",
    "Assertion",
    "Fatal failure",
    "Internal error detected",
    "an invalid model was generated",
    "Failed to verify",
    "failed to verify",
    "ERROR: AddressSanitizer:",
    "Aborted"
]

def get_logic(logic):
    logic_ = 0
    if "ALL"==logic:
        logic_ = (logic_ | 127)
    if "S" in logic:
        logic_ = (logic_ | 4)
    if "I" in logic:
        logic_ = (logic_ | 2)
    if "R" in logic:
        logic_ = (logic_ | 1)
    return logic_

def calculate_model(model_info,solver):
    model_res = None
    var = model_info[0]
    if solver=="dreal":
        var = model_info[0]
        value_type = model_info[1]
        if value_type=="Real":
            if len(model_info)>=4:
                if model_info[2][1]=='-':
                    value_model_lower = -float(model_info[2][2:-1])
                else:
                    value_model_lower = float(model_info[2][1:-1])
                if model_info[3][0]=='-':
                    value_model_upper = float(model_info[3][1:-1])
                else:
                    value_model_upper = float(model_info[3][:-1])
                model_res = interval[value_model_lower,value_model_upper]
            elif len(model_info)==3:
                if model_info[2][0]=='-':
                    value_model = -float(model_info[2][1:])
                else:
                    value_model = float(model_info[2])
                model_res = interval(value_model)
        elif value_type=="Int":
            if model_info[2][0]=="-":
                    value_model = -int(model_info[2][1:])
            else:
                value_model = int(model_info[2])
            model_res = interval(value_model)
        elif value_type=="Bool":
            model_res = (value_model=="true")
        else:
            pass
    elif solver =="cvc":
        var = model_info[0]
        v_type = model_info[1]
        if v_type == "Real":
            if len(model_info)>5:
                model_res = None
            elif len(model_info)==5:
                model_res = None
            elif len(model_info)==4:
                value = model_info[-1]
                if "?" in value:  
                    value=re.sub(r"[?]","",value)  
                    l = value+"0"
                    u = value+"9"
                    model_res = interval[-float(u),-float(l)]
                else:
                    model_res = interval(-float(value))
            else:
                value = model_info[-1]
                if "?" in value:
                    value=re.sub(r"[?]","",value)  
                    l = value+"0"
                    u = value+"9"
                    model_res = interval[float(u),float(l)]
                else:
                    model_res = interval(float(value))
        elif v_type == "Int":
            if len(model_info)>=5:
                pass
            elif len(model_info)==4:
                model_res = interval(-int(model_info[-1]))
            else:
                model_res = interval(int(model_info[-1]))
        elif v_type == "Bool":
            if len(model_info)>=4:
                pass
            else:
                val = model_info[-1]
                model_res = (val=="true")
        elif v_type == "String":
            if len(model_info)>=4:
                if model_info[2]=='"' and model_info[3]=='"':
                    model_res = '" "'
                else:
                    pass
            else:
                model_res = model_info[-1]
        else:
            pass
    elif solver=="z3":
        var = model_info[0]
        v_type = model_info[1]
        if v_type == "Real":
            if len(model_info)>5:
                model_res = None
            elif len(model_info)==5:
                model_res = None
            elif len(model_info)==4:
                value = model_info[-1]
                if "?" in value:  
                    value=re.sub(r"[?]","",value)  
                    l = value+"0"
                    u = value+"9"
                    model_res = interval[-float(u),-float(l)]
                else:
                    model_res = interval(-float(value))
            else:
                value = model_info[-1]
                if "?" in value:
                    value=re.sub(r"[?]","",value)  
                    l = value+"0"
                    u = value+"9"
                    model_res = interval[float(u),float(l)]
                else:
                    model_res = interval(float(value))
        elif v_type == "Int":
            if len(model_info)>4:
                model_res = None
            elif len(model_info)==4:
                model_res = interval(-int(model_info[-1]))
            else:
                model_res = interval(int(model_info[-1]))
        elif v_type == "Bool":
            if len(model_info)>=4:
                pass
            else:
                val = model_info[-1]
                model_res = (val=="true")
        elif v_type == "String":
            if len(model_info)>=4:
                if model_info[2]=='"' and model_info[3]=='"':
                    model_res = '" "'
                else:
                    pass
            else:
                model_res = model_info[-1]
    else:
        pass
    return model_res


def run_solver(file_path,solver,solverbin,timeout,option=None,var=None):
    if option is None:
        option = []
    if solver=="dreal":
        cmd = [solverbin,file_path]
    elif solver == "cvc":
        cmd = [solverbin,'--check-models','--produce-models']+option+[file_path]
    elif solver == "z3":
        cmd = [solverbin,'model_validate=true']+option+[file_path]      
    else:
        print(option)
        return [None,"error"]

    try:
        output = subprocess.run(
            cmd,
            timeout = int(timeout),
            stdout = subprocess.PIPE,
            stderr = subprocess.PIPE,
            shell = False
        )
    except subprocess.TimeoutExpired as t:
        return [None,"timeout"]

    stdout = output.stdout.decode()
    stderr = output.stderr.decode()
    stream = stdout+" "+stderr
    for err in crash_list:
        if err in stream:
            if "The exponent of the POW(^)" in stream:
                print("Pow(^) error")
                return None,"error"
            return err, "crash"
    
    lines = stream.splitlines()
    res = ""
    lines = [x for x in lines]
    while "unsupported" in lines:
        lines.remove("unsupported")

    if len(lines) > 0:
        if "unsat" in lines:
            return [None,"unsat"]
        elif "unknown" in lines:
            return [None,"unknown"]
        elif not("sat" in lines or "delta-sat" in lines[0]):
            return [None,"error"]
    else:
        return [None,"timeout"]

    if len(lines) >= 2 and "an invalid model was generated" in lines[1]:
        return [None,"invalid"]

    if var is None:
        return [None,"sat"]


    while '(' in lines:
        lines.remove('(')
    while ')' in lines:
        lines.remove(')')
    lines = lines[1:]
    lines = ''.join(lines).split()
    lines = ' '.join(lines).split("(define-fun")
    lines = lines[1:]
    model = {}
    for line in lines:
        line = re.sub(r"[()]","",line)
        model_info = line.split()
        if model_info[1]=="String":
            d = ""
            for c in model_info[2:-1]:
                d+=c+" "
            d+=model_info[-1]
            model_info = [model_info[0],model_info[1],d]
        if model_info[0] in var:
            var_model = calculate_model(model_info,solver)
            model[model_info[0]] = var_model
        elif model_info[0]!="/0":
            continue
    return [model,"sat"]


def get_model(seed, ast, solver, var, logic):
    if solver == "z3":
        res, model, declare_part, data = get_z3_model(seed, var)
        if res != "sat":
            return None, res
        m = {}
        for v in model:
            m[v] = model[v]
        solver_data = {"solver": solver, "data":declare_part, "model" : model, "vars": data}
    elif solver =="cvc":
        res, model, data = get_cvc5_model(ast,logic)
        m = model
        if res != "sat":
            return None, res
        solver_data = {"solver": solver, "data":data, "model" : model, "vars": data}
    else:
        solver_data = {"solver": solver, "data":None, "model" : None}
        data = {}
        m = {}
        model = None
    return solver_data, m

def get_z3_model(smt2, var):
    smt2_file = parse_smt2_file(smt2)
    s = z3.Solver()
    s.set("timeout", 10000) # set timeout option 10s
    set_option("model_validate","true")
    s.add(smt2_file)
    res = s.check()
    vars = {}
    if res == z3.sat:
        m = s.model()
        declare_part = ""
        for v in list(var.keys()):
            declare_part += "(declare-fun "+v+" () "+var[v]+")"
            if "Bool" in var[v]:
                vars[v] = Bool(v)
            elif "Int" in var[v]:
                vars[v] = Int(v)
            elif "Real" in var[v]: 
                vars[v] = Real(v)
            elif "String" in var[v]:
                vars[v] = String(v)
        return "sat", m, declare_part,vars
    elif res == z3.unsat:
        return "unsat", None, None, None
    elif res == z3.unknown:
        return "unknown", None, None, None
    else: 
        return "error", None, None, None

def get_cvc5_model(smt2,logic):
    s = cvc5.Solver()
    s.setLogic("ALL")
    s.setOption("strings-exp","true")
    s.setOption("tlimit-per","10000")
    s.setOption("produce-models","true")
    s.setOption("check-models","true")

    vars = {}
    for a in smt2:
        if "declare" in a[1]:
            if "Bool" in a[-2]:
                vars[a[2]] = s.mkConst(s.getBooleanSort(),a[2])
            elif "Int" in a[-2]:
                vars[a[2]] = s.mkConst(s.getIntegerSort(),a[2])
            elif "Real" in a[-2]: 
                vars[a[2]] = s.mkConst(s.getRealSort(),a[2])
            elif "String" in a[-2]:
                vars[a[2]] = s.mkConst(s.getStringSort(),a[2])
    
    l = get_logic(logic)
    for a in smt2:
        if a[1]=="assert":
            cvc_ast = ast_to_cvc5(a[2],s,vars,l)
            s.assertFormula(cvc_ast)

    res = s.checkSat()
    if cvc5.Result.isSat(res):
        return "sat", s, vars
    else:
        return "unsat", None, None
