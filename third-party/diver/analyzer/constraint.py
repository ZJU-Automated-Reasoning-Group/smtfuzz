import math
import numpy as np
from analyzer.func import *
from functools import reduce
from interval import interval, imath, fpu, inf


def analyze_logic_op(p_op, p_cond, siblings_eval, e, midx):
    cond = e
    if p_op == "and":
        if p_cond == [True, False] or p_cond == True:
            cond = p_cond
        else:
            s_eval = reduce(lambda res, cur: res | cur, siblings_eval)
            if s_eval == False:
                cond = [True, False]
            else:
                cond = False
    elif p_op == "or":
        if p_cond == [True, False] or p_cond == False:
            cond = p_cond
        else:
            s_eval = reduce(lambda res, cur: res | cur, siblings_eval)
            if s_eval == True:
                cond = [True, False]
            else:
                cond = True
    elif p_op == "xor":
        if p_cond == [True, False]:
            cond = p_cond
        elif p_cond == True:
            s_eval = reduce(lambda res, cur: res ^ cur, siblings_eval)
            if s_eval == True:
                cond = False
            else:
                cond = True
        else:
            s_eval = reduce(lambda res, cur: res ^ cur, siblings_eval)
            if s_eval == True:
                cond = True
            else:
                cond = False
    elif p_op == "=>":
        if p_cond == [True, False]:
            cond = p_cond
        elif p_cond == True:
            if midx == 0:
                cond = ([True, False] if siblings_eval[0] == True else False)
            else:
                cond = ([True, False] if siblings_eval[0] == False else True)
        else:
            pass
    elif p_op == "not":
        if p_cond == [True, False]:
            cond = p_cond
        else:
            cond = not (p_cond)
    elif p_op == "ite":
        pass
    else:
        pass
    return cond


def analyze_cop_op(t, p_op, p_cond, siblings_eval, e, midx):
    cond = e
    if p_op == "=":
        if t == "Bool":
            if p_cond == [True, False]:
                cond = [True, False]
            elif p_cond == True:
                cond = siblings_eval[0]
            else:
                s_eval = (True in siblings_eval) and (False in siblings_eval)
                if s_eval:
                    cond = [True, False]
                else:
                    cond = not (True in siblings_eval)
        elif t == "Real":
            if p_cond == [True, False]:
                cond = interval[-inf, inf]
            elif p_cond == False:
                pass
            else:
                cond = siblings_eval[0]
        elif t == "Int":
            if p_cond == [True, False]:
                cond == interval[-inf, inf]
            elif p_cond == False:
                pass
            else:
                cond = siblings_eval[0]
        elif t == "String":
            pass
        else:
            pass
    elif p_op == "distinct":
        if t == "Bool":
            if p_cond == [True, False]:
                cond = [True, False]
            elif p_cond == False:
                cond = siblings_eval[0]
            else:
                s_eval = (True in siblings_eval) and (False in siblings_eval)
                if s_eval:
                    cond = [True, False]
                else:
                    cond = not (True in siblings_eval)
        elif t == "Real":
            if p_cond == [True, False]:
                cond = interval[-inf, inf]
            elif p_cond == False:
                pass
            else:
                pass
        elif t == "Int":
            if p_cond == [True, False]:
                cond = interval[-inf, inf]
            elif p_cond == False:
                pass
            else:
                pass
        elif t == "String":
            pass
        else:
            pass
    elif p_op == "<=":
        if p_cond == [True, False]:
            cond = interval[-inf, inf]
        elif p_cond == True:
            l, u = [-inf, inf]
            if midx != 0:
                l, _ = fpu.min(siblings_eval[midx - 1])
            if midx != len(siblings_eval):
                _, u = fpu.max(siblings_eval[midx])
            cond = interval[l, u]
        else:
            l, u = [-inf, inf]
            if midx != 0:
                _, u = fpu.min(siblings_eval[midx - 1])
                u = (math.floor(u - (1e-10)) if t == "Int" else u - 1e-10)
            if midx != len(siblings_eval):
                l, _ = fpu.max(siblings_eval[midx])
                l = (math.ceil(l + (1e-10)) if t == "Int" else l + 1e-10)
            cond = interval[l, u]
    elif p_op == "<":
        if p_cond == [True, False]:
            cond = interval[-inf, inf]
        elif p_cond == True:
            l, u = [-inf, inf]
            if midx != 0:
                l, _ = fpu.min(siblings_eval[midx - 1])
                l = (math.ceil(l + (1e-10)) if t == "Int" else l + 1e-10)
            if midx != len(siblings_eval):
                _, u = fpu.max(siblings_eval[midx])
                u = (math.floor(u - (1e-10)) if t == "Int" else u - 1e-10)
            cond = interval[l, u]
        else:
            l, u = [-inf, inf]
            if midx != 0:
                _, u = fpu.min(siblings_eval[midx - 1])
            if midx != len(siblings_eval):
                l, _ = fpu.max(siblings_eval[midx])
            cond = interval[l, u]
    elif p_op == ">=":
        if p_cond == [True, False]:
            cond = interval[-inf, inf]
        elif p_cond == True:
            l, u = [-inf, inf]
            if midx != 0:
                _, u = fpu.min(siblings_eval[midx - 1])
            if midx != len(siblings_eval):
                l, _ = fpu.max(siblings_eval[midx])
            cond = interval[l, u]
        else:
            l, u = [-inf, inf]
            if midx != 0:
                l, _ = fpu.min(siblings_eval[midx - 1])
                l = (math.ceil(l + (1e-10)) if t == "Int" else l + 1e-10)
            if midx != len(siblings_eval):
                _, u = fpu.max(siblings_eval[midx])
                u = (math.floor(u - (1e-10)) if t == "Int" else u - 1e-10)
            cond = interval[l, u]
    elif p_op == ">":
        if p_cond == [True, False]:
            cond = interval[-inf, inf]
        elif p_cond == True:
            l, u = [-inf, inf]
            if midx != 0:
                _, u = fpu.min(siblings_eval[midx - 1])
                u = (math.floor(u - (1e-10)) if t == "Int" else u - 1e-10)
            if midx != len(siblings_eval):
                l, _ = fpu.max(siblings_eval[midx])
                l = (math.ceil(l + (1e-10)) if t == "Int" else l + 1e-10)
            cond = interval[l, u]
        else:
            l, u = [-inf, inf]
            if midx != 0:
                l, _ = fpu.min(siblings_eval[midx - 1])
            if midx != len(siblings_eval):
                _, u = fpu.max(siblings_eval[midx])
            cond = interval[l, u]
    else:
        pass
    return cond


def analyze_real_op(t, p_op, p_cond, node, siblings_eval, e, m_idx, e_dict, t_dict):
    cond = e
    pi = interval(np.arctan(1) * 4)
    if p_op == "tanh":
        p_cond = p_cond & interval[-1.0 + (1e-8), 1.0 - (1e-8)]
        cond = 0.5 * imath.log((1.0 + p_cond) / (1.0 - p_cond))
    elif p_op == "cosh":
        p_cond = p_cond & interval[1.0, inf]
        cond = imath.log(p_cond + imath.sqrt(pow(p_cond, 2) - 1))
    elif p_op == "sinh":
        cond = imath.log(p_cond + imath.sqrt(pow(p_cond, 2) + 1))
    elif p_op in ["arctan2", "atan2"]:
        pass
    elif p_op in ["arctan", "atan"]:
        p_cond = p_cond & interval[(-pi / 2.0) + 1e-9, pi / 2.0 - (1e-9)]
        cond = imath.tan(p_cond)
    elif p_op in ["arccos", "acos"]:
        p_cond = p_cond & interval[0, pi]
        cond = imath.cos(p_cond)
    elif p_op in ["arcsin", "asin"]:
        p_cond = p_cond & interval[-pi / 2.0, pi / 2.0]
        cond = imath.sin(p_cond)
    elif p_op == "tan":
        cond = [imath.atan(p_cond) & interval[-pi / 2.0 + (1e-9), pi / 2.0 - (1e-9)]]
        for i in range(5):
            cond.append(cond[0] + 2 * np.pi * (i + 1))
            cond.append(cond[0] - 2 * np.pi * (i + 1))
        cond = interval.union(cond)
    elif p_op == "cos":
        cond = [acos(p_cond)]
        for i in range(5):
            cond.append(cond[0] + 2 * np.pi * (i + 1))
            cond.append(cond[0] - 2 * np.pi * (i + 1))
        cond = interval.union(cond)
    elif p_op == "sin":
        cond = [asin(p_cond)]
        for i in range(5):
            cond.append(cond[0] + 2 * np.pi * (i + 1))
            cond.append(cond[0] - 2 * np.pi * (i + 1))
        cond = interval.union(cond)
    elif p_op == "log":
        cond = imath.exp(p_cond)
    elif p_op == "exp":
        p_cond = p_cond & interval[1e-9, inf]
        cond = imath.log(p_cond)
    elif p_op == "to_real":
        pass
    elif p_op == "/":
        if p_cond == interval[-inf, inf]:
            if m_idx == 0:
                cond = p_cond
            else:
                cond = e
        else:
            t_dict[node] -= 1
            terms = list(t_dict.keys())
            cond = interval(1.0)
            mask = interval[-1e-8, 1e-8]
            if m_idx == 0:
                for term in terms:
                    if t_dict[term] == 0:
                        continue
                    l = pow(e_dict[term], interval(t_dict[term]))
                    if cond == interval(0.0) or l == interval(0.0) or mask & l == mask:
                        cond = interval(0.0)
                        continue
                    cond *= l
                if interval([inf]) in cond or interval([-inf]) in cond:
                    cond = 0
                else:
                    cond = p_cond * cond
            else:
                t_dict[terms[0]] -= 1
                cond *= e_dict[terms[0]]
                for term in terms:
                    if t_dict[term] == 0:
                        continue
                    l = pow(e_dict[term], interval(t_dict[term]))
                    if cond == interval(0.0) or l == interval(0.0) or mask & l == mask:
                        cond = interval(0.0)
                        continue
                    cond *= l
                if interval([inf]) in cond or interval([-inf]) in cond:
                    cond = 0
                else:
                    cond = cond / p_cond
    elif p_op == "csc":
        pass
    elif p_op == "sec":
        pass
    elif p_op == "cot":
        pass
    elif p_op == "arccsc":
        pass
    elif p_op == "arcsec":
        pass
    elif p_op == "arccot":
        pass
    else:
        pass
    return cond


def analyze_int_op(t, p_op, p_cond, siblings_eval, e, midx):
    cond = e
    if p_op == "to_int":
        cond = []
        for si in p_cond:
            l, u = si
            cond.append(interval[l, u + 0.9999999])
        cond = interval.union(cond)
    elif p_op == "div":
        pass
    elif p_op == "mod":
        pass
    elif p_op == "int.pow2":
        pass
    else:
        pass
    return cond


def analyze_arith_op(t, p_op, p_cond, node, siblings_eval, e, midx, e_dict, t_dict):
    cond = e
    real = interval[-inf, inf]
    if p_op in ["pow", "^"]:
        pass
    elif p_op == "sqrt":
        pass
    elif p_op == "max":
        pass
    elif p_op == "min":
        pass
    elif p_op == "abs":
        pass
    elif p_op == "*":
        if p_cond == real:
            cond = real
        else:
            t_dict[node] -= 1
            terms = list(t_dict.keys())
            cond = interval(1.0)
            mask = interval[-1e-8, 1e-8]
            for term in terms:
                if t_dict[term] == 0:
                    continue
                l = pow(e_dict[term], interval(t_dict[term]))
                if cond == interval(0.0) or l == interval(0.0) or mask & l == mask:
                    cond = interval(0.0)
                    continue
                cond *= l
            if interval([inf]) in cond or interval([-inf]) in cond:
                cond = e
            else:
                cond = p_cond / cond
    elif p_op == "+":
        if p_cond == real:
            cond = real
        else:
            t_dict[node] -= 1
            terms = list(t_dict.keys())
            cond = interval(0.0)
            for term in terms:
                cond += e_dict[term] * interval(t_dict[term])
            cond = p_cond - cond
    elif p_op == "-":
        if p_cond == real:
            cond = real
        else:
            if len(siblings_eval) == 0:
                cond = p_cond * interval(-1.0)
            else:
                t_dict[node] -= 1
                terms = list(t_dict.keys())
                cond = interval(0.0)
                if midx == 0:
                    for term in terms:
                        cond += e_dict[term] * interval(t_dict[term])
                    cond = p_cond + cond
                else:
                    t_dict[terms[0]] -= 1
                    cond = e_dict[terms[0]]
                    for term in terms:
                        cond -= e_dict[term] * interval(t_dict[term])
                    cond = cond - p_cond
    else:
        pass
    return cond


def analyze_string_op(t, p_op, p_cond, node, siblings_eval, e, midx, e_dict, t_dict):
    cond = e
    return cond


def analyze_reg_op(t, p_op, p_cond, node, siblings_eval, e, midx, e_dict, t_dict):
    cond = e
    return cond
