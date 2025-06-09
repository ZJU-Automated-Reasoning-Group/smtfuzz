import numpy as np
import math
import re
import rstr
import warnings
from utils.debug import trace
from analyzer.func import *
from interval import interval, imath, fpu, inf
from functools import reduce

warnings.simplefilter(action='ignore', category=FutureWarning)


@trace
def eval_logic_op(op, E, T):
    t = "Bool"
    if op == "and":
        e = reduce(lambda res, cur: res & cur, E)
    elif op == "or":
        e = reduce(lambda res, cur: res | cur, E)
    elif op == "xor":
        e = reduce(lambda res, cur: res ^ cur, E)
    elif op == "not":
        e = not (E[0])
    elif op == "=>":
        e = (False if (E[0] == True and E[1] == False) else True)
    elif op == "ite":
        e = (E[1] if E[0] == True else E[2])
        t = (T[1] if E[0] == True else T[2])
    else:
        e = None
    return e, t


@trace
def eval_cop_op(op, E, T):
    t = "Bool"
    if op == "=":
        if T[0] == "String":
            e = True
            tmp_s = from_uni(E[0][1:-1])
            for i in range(1, len(E)):
                e = e & (tmp_s == from_uni(E[i][1:-1]))
        elif T[0] == "Bool":
            e = True
            tmp_b = E[0]
            for i in range(1, len(E)):
                e = e & (tmp_b == E[i])
        else:
            e = True
            for i in E:
                for j in E:
                    j = j + interval[-1e-10, 1e-10]
                    e = e & (not (i & j == interval()))
    elif op == "distinct":
        e_dict = set()
        e = True
        if T[0] == "String":
            tmp_s = from_uni(E[0][1:-1])
            e_dict.add(tmp_s)
            for i in range(1, len(E)):
                e = e & (not (from_uni(E[i][1:-1]) in e_dict))
                e_dict.add(from_uni(E[0][1:-1]))
        elif T[0] == "Bool":
            e = True
            tmp_b = E[0]
            for i in range(1, len(E)):
                e = e & (not (tmp_b == E[i]))
        else:
            e_dict.add(E[0])
            for i in range(len(E)):
                a_i = E[i] + interval[-1e-8, 1e-8]
                for j in range(i + 1, len(E)):
                    a_j = E[j] + interval[-1e-8, 1e-8]
                    e = e & (not (a_i & E[j] == E[j] and a_j & E[i] == E[i]) or (a_i & a_j == interval()))
    elif op == ">=":
        e = True
        _, u = fpu.min(E[0])
        for i in range(1, len(E)):
            l, _ = fpu.min(E[i])
            e = e & (l <= u + 1e-7)
            _, u = fpu.max(E[i])
    elif op == ">":
        e = True
        _, u = fpu.min(E[0])
        ca = True
        for i1 in range(len(E)):
            i = E[i1]
            for i2 in range(i1 + 1, len(E)):
                j = E[i2]
                ca = ca & (not (i & j == interval()))

        if ca == False:
            for i in range(1, len(E)):
                l, _ = fpu.min(E[i])
                e = e & (l < u + 1e-10)
                _, u = fpu.max(E[i])
        else:
            e = False
    elif op == "<=":
        e = True
        l, _ = fpu.min(E[0])
        for i in range(1, len(E)):
            _, u = fpu.max(E[i])
            e = e & (l <= u + 1e-7)
            l, _ = fpu.min(E[i])
    elif op == "<":
        e = True
        ca = True
        for i1 in range(len(E)):
            i = E[i1]
            for i2 in range(i1 + 1, len(E)):
                j = E[i2]
                ca = ca & (not (i & j == interval()))
        if ca == False:
            l, _ = fpu.min(E[0])
            for i in range(1, len(E)):
                _, u = fpu.max(E[i])
                e = e & (l < u + 1e-10)
                l, _ = fpu.min(E[i])
        else:
            e = False
    return e, t


@trace
def eval_real_op(op, E, T):
    t = "Real"
    if op == "tanh":
        e = imath.tanh(E[0])
    elif op == "cosh":
        e = imath.cosh(E[0])
    elif op == "sinh":
        e = imath.sinh(E[0])
    elif op in ["arctan", "atan"]:
        e = imath.atan(E[0])
    elif op in ["arccos", "acos"]:
        e = acos(E[0])
    elif op in ["arcsin", "asin"]:
        e = asin(E[0])
    elif op == "tan":
        e = imath.tan(E[0])
    elif op == "cos":
        e = imath.cos(E[0])
    elif op == "sin":
        e = imath.sin(E[0])
    elif op == "log":
        if E[0] <= interval(0.0) + 1e-8:
            e = None
        else:
            e = imath.log(E[0])
    elif op == "exp":
        e = imath.exp(E[0])
    elif op == "to_real":
        e = E[0]
    elif op == "/":
        e = E[0] / E[1]
    elif op in ["arctan2", "atan2"]:
        e = arctan2(E[0], E[1])
    else:
        e = None
    return e, t


@trace
def eval_int_op(op, E, T):
    t = "Int"
    if op == "to_int":
        e = []
        for s in E[0]:
            l, u = s
            l = int(math.floor(float(l)))
            u = int(math.floor(float(u)))
            e.append(interval[l, u])
        e = interval.union(e)
    elif op == "div":
        e = E[0] / E[1]
    elif op == "mod":
        if E[0] == interval():
            return None, None
        l1, u1 = E[0][0]
        if E[1] == interval():
            return None, None
        l2, u2 = E[1][0]
        e = []
        for p in range(int(l1), min(int(l1) + 100, int(u1) + 1)):
            for s in range(int(l2), min(int(l2) + 100, int(u2) + 1)):
                if s == 0:
                    continue
                if s < 0:
                    e.append(interval(p % (-s)))
                else:
                    e.append(interval(p % s))
        e = interval.union(e)
    elif op == "int.pow2":
        e = []
        for s in E[0]:
            l, u = s
            l = int(math.pow(2, min(512, int(l))))
            u = int(math.pow(2, min(512, int(u))))
            e.append(interval(l, u))
        e = interval.union(e)
    elif op == "iand":
        s1, _ = E[0][0]
        s2, _ = E[1][0]
        s3, _ = E[2][0]
        e = s1 % (s2 & s3)
    else:
        e = None
    return e, t


@trace
def eval_arith_op(op, E, T):
    if op in ["pow", "^"]:
        t = "Real"
        e = pow(E[0], E[1])
    elif op == "sqrt":
        t = "Real"
        e = imath.sqrt(E[0])
    elif op == "max":
        t = T[0]
        e = E[0]
    elif op == "min":
        t = T[0]
        e = E[0]
    elif op == "+":
        e = interval(0)
        for e_i in E:
            e += e_i
        t = ("Real" if ("Real" in T) else "Int")
    elif op == "-":
        if len(E) == 1:
            e = -E[0]
            t = T[0]
        else:
            e = E[0]
            e = interval(0)
            for id in range(1, len(E)):
                e -= E[id]
            t = "Real" if "Real" in T else "Int"
    elif op == "*":
        e = E[0] * E[1]
        t = "Real" if ("Real" in T) else "Int"
    elif op == "abs":
        t = T[0]
        e = abs(E[0])
    else:
        e = None
        t = None
    return e, t
