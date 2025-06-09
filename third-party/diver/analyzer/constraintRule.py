import math
import numpy as np
import cvc5
from cvc5 import Kind
from z3 import *
from functools import reduce
from interval import interval, imath, fpu, inf


def get_logic_constraint(parent_op, parent_cond, cur_eval, cur_ty, node_idx, sub_evaluations):
    if cur_ty in ["Bool", "String", "RegLan"]:
        constraint = cur_eval
    else:
        constraint = {"l": cur_eval, "u": cur_eval}

    if parent_op == "and":
        if parent_cond == [True, False] or parent_cond:
            constraint = parent_cond
        else:
            tmp_eval = reduce(lambda res, cur: res | cur, sub_evaluations)
            if tmp_eval:
                constraint = False
            else:
                constraint = [True, False]
    elif parent_op == "or":
        if parent_cond == [True, False] or not (parent_cond):
            constraint = parent_cond
        else:
            tmp_eval = reduce(lambda res, cur: res | cur, sub_evaluations)
            if tmp_eval:
                constraint = [True, False]
            else:
                constraint = True
    elif parent_op == "xor":
        if parent_cond == [True, False]:
            costraint = parent_cond
        else:
            tmp_eval = reduce(lambda res, cur: res ^ cur, sub_evaluations)
            constraint = (parent_cond != tmp_eval)
    elif parent_op == "=>":
        if parent_cond == [True, False]:
            constraint = parent_cond
        elif parent_cond:
            if node_idx == 0:
                constraint = [True, False] if sub_evaluations[0] else False
            else:
                constraint = [True, False] if not (sub_evaluations[0]) else True
        else:
            pass
    elif parent_op == "not":
        if parent_cond == [True, False]:
            constraint = parent_cond
        else:
            constraint = not (parent_cond)
    elif parent_op == "ite":
        pass
    elif parent_op == "iand":
        pass
    else:
        pass
    return constraint


def get_eq_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations):
    if cur_type in ["Bool", "String"]:
        constraint = cur_eval
    else:
        constraint = {"l": cur_eval, "u": cur_eval}
    if parent_op == "=":
        if cur_type == "Bool":
            if parent_cond == [True, False]:
                constraint = [True, False]
            elif parent_cond:
                constraint = sub_evaluations[0]
            else:
                tmp_eval = (True in sub_evaluations) and (False in sub_evaluations)
                if tmp_eval:
                    constraint = [True, False]
                else:
                    constraint = not (True in sub_evaluations)
        elif cur_type in ["Int", "Real"]:
            if parent_cond == [True, False]:
                constraint = {"l": -inf, "u": inf}
            else:
                pass
        elif cur_type == "String":
            if parent_cond == [True, False]:
                constraint = "(.)*"
            else:
                pass
        else:
            pass
    elif parent_op == "distinct":
        if cur_type == "Bool":
            if parent_cond == [True, False]:
                constraint = [True, False]
            elif not (parent_cond):
                constraint = sub_evaluations[0]
            else:
                tmp_eval = (True in sub_evaluations) and (False in sub_evaluations)
                if tmp_eval:
                    constraint = [True, False]
                else:
                    constraint = not (True in sub_evaluations)
        elif cur_type in ["Int", "Real"]:
            if parent_cond == [True, False]:
                constraint = {"l": -inf, "u": inf}
            else:
                pass
        elif cur_type == "String":
            if parent_cond == [True, False]:
                constraint = "(.)*"
            else:
                pass
        else:
            pass
    else:
        pass
    return constraint


def get_compare_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, solver,
                           model):
    constraint = {"l": cur_eval, "u": cur_eval}
    if parent_cond == [True, False]:
        return {"l": -inf, "u": inf}
    if parent_op == "<":
        if parent_cond:
            if node_idx == 0:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[0] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": -inf, "u": model.getValue(
                            model.mkTerm(Kind.SUB, sub_api_terms[0], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[0] - (1e-6)}
                else:
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[0] - (1))}
                    elif solver == "cvc":
                        constraint = {"l": -inf,
                                      "u": model.getValue(model.mkTerm(Kind.SUB, sub_api_terms[0], model.mkInteger(1)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[0] - interval(1)}
            elif node_idx == len(sub_evaluations):
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[-1] + (1e-6)), "u": inf}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[-1], model.mkReal(1, 100000))),
                            "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[-1] + (1e-6), "u": inf}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[-1] + 1), "u": inf}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[-1], model.mkInteger(1))),
                            "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[-1] + interval(1.0), "u": inf}
            else:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx - 1] + 1e-6),
                                      "u": simplify(sub_evaluations[node_idx] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(
                            model.mkTerm(Kind.ADD, sub_api_terms[node_idx - 1], model.mkReal(1, 100000))),
                                      "u": model.getValue(
                                          model.mkTerm(Kind.SUB, sub_api_terms[node_idx], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx - 1] + 1e-6, "u": sub_evaluations[node_idx] - 1e-6}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx - 1] + 1),
                                      "u": simplify(sub_evaluations[node_idx] - (1))}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(
                            model.mkTerm(Kind.ADD, sub_api_terms[node_idx - 1], model.mkInteger(1))),
                                      "u": model.getValue(
                                          model.mkTerm(Kind.SUB, sub_api_terms[node_idx], model.mkInteger(1)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx - 1] + interval(1.0),
                                      "u": sub_evaluations[node_idx] - interval(1)}
        else:
            if node_idx == 0:
                constraint = {"l": sub_evaluations[0], "u": inf}
            elif node_idx == len(sub_evaluations):
                constraint = {"l": -inf, "u": sub_evaluations[-1]}
            else:
                constraint = {"l": sub_evaluations[node_idx], "u": sub_evaluations[node_idx - 1]}
    elif parent_op == "<=":
        if parent_cond:
            if node_idx == 0:
                constraint = {"l": -inf, "u": sub_evaluations[0]}
            elif node_idx == len(sub_evaluations):
                constraint = {"l": sub_evaluations[-1], "u": inf}
            else:
                constraint = {"l": sub_evaluations[node_idx - 1], "u": sub_evaluations[node_idx]}
        else:
            if node_idx == 0:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[0] + (1e-6)), "u": inf}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[0], model.mkReal(1, 100000))),
                            "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[0] + (1e-6), "u": inf}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[0] + 1), "u": inf}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[0], model.mkInteger(1))),
                                      "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[0] + interval(1), "u": inf}
            elif node_idx == len(sub_evaluations):
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[-1] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": -inf, "u": model.getValue(
                            model.mkTerm(Kind.SUB, sub_api_terms[-1], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[-1] - (1e-6)}
                else:
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[-1] - (1))}
                    elif solver == "cvc":
                        constraint = {"l": -inf, "u": model.getValue(
                            model.mkTerm(Kind.SUB, sub_api_terms[-1], model.mkInteger(1)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[-1] - interval(1)}
            else:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx] + 1e-6),
                                      "u": simplify(sub_evaluations[node_idx - 1] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(
                            model.mkTerm(Kind.ADD, sub_api_terms[node_idx], model.mkReal(1, 100000))),
                                      "u": model.getValue(
                                          model.mkTerm(Kind.SUB, sub_api_terms[node_idx - 1], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx] + 1e-6, "u": sub_evaluations[node_idx - 1] - 1e-6}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx] + 1),
                                      "u": simplify(sub_evaluations[node_idx - 1] - (1))}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[node_idx], model.mkInteger(1))),
                            "u": model.getValue(
                                model.mkTerm(Kind.SUB, sub_api_terms[node_idx - 1], model.mkInteger(1)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx] + interval(1.0),
                                      "u": sub_evaluations[node_idx - 1] - interval(1)}
    elif parent_op == ">":
        if parent_cond:
            if node_idx == 0:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[0] + (1e-6)), "u": inf}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[0], model.mkReal(1, 100000))),
                            "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[0] + (1e-6), "u": inf}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[0] + 1), "u": inf}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[0], model.mkInteger(1))),
                                      "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[0] + interval(1), "u": inf}
            elif node_idx == len(sub_evaluations):
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[-1] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": -inf, "u": model.getValue(
                            model.mkTerm(Kind.SUB, sub_api_terms[-1], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[-1] - (1e-6)}
                else:
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[-1] - (1))}
                    elif solver == "cvc":
                        constraint = {"l": -inf, "u": model.getValue(
                            model.mkTerm(Kind.SUB, sub_api_terms[-1], model.mkInteger(1)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[-1] - interval(1)}
            else:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx] + 1e-6),
                                      "u": simplify(sub_evaluations[node_idx - 1] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(
                            model.mkTerm(Kind.ADD, sub_api_terms[node_idx], model.mkReal(1, 100000))),
                                      "u": model.getValue(
                                          model.mkTerm(Kind.SUB, sub_api_terms[node_idx - 1], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx] + 1e-6, "u": sub_evaluations[node_idx - 1] - 1e-6}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx] + 1),
                                      "u": simplify(sub_evaluations[node_idx - 1] - (1))}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[node_idx], model.mkInteger(1))),
                            "u": model.getValue(
                                model.mkTerm(Kind.SUB, sub_api_terms[node_idx - 1], model.mkInteger(1)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx] + interval(1.0),
                                      "u": sub_evaluations[node_idx - 1] - interval(1)}
        else:
            if node_idx == 0:
                constraint = {"l": -inf, "u": sub_evaluations[0]}
            elif node_idx == len(sub_evaluations):
                constraint = {"l": sub_evaluations[-1], "u": inf}
            else:
                constraint = {"l": sub_evaluations[node_idx - 1], "u": sub_evaluations[node_idx]}
    elif parent_op == ">=":
        if parent_cond:
            if node_idx == 0:
                constraint = {"l": sub_evaluations[0], "u": inf}
            elif node_idx == len(sub_evaluations):
                constraint = {"l": -inf, "u": sub_evaluations[-1]}
            else:
                constraint = {"l": sub_evaluations[node_idx], "u": sub_evaluations[node_idx - 1]}
        else:
            if node_idx == 0:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[0] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": -inf, "u": model.getValue(
                            model.mkTerm(Kind.SUB, sub_api_terms[0], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[0] - (1e-6)}
                else:
                    if solver == "z3":
                        constraint = {"l": -inf, "u": simplify(sub_evaluations[0] - (1))}
                    elif solver == "cvc":
                        constraint = {"l": -inf,
                                      "u": model.getValue(model.mkTerm(Kind.SUB, sub_api_terms[0], model.mkInteger(1)))}
                    else:
                        constraint = {"l": -inf, "u": sub_evaluations[0] - interval(1)}
            elif node_idx == len(sub_evaluations):
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[-1] + (1e-6)), "u": inf}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[-1], model.mkReal(1, 100000))),
                            "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[-1] + (1e-6), "u": inf}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[-1] + 1), "u": inf}
                    elif solver == "cvc":
                        constraint = {
                            "l": model.getValue(model.mkTerm(Kind.ADD, sub_api_terms[-1], model.mkInteger(1))),
                            "u": inf}
                    else:
                        constraint = {"l": sub_evaluations[-1] + interval(1.0), "u": inf}
            else:
                if cur_type == "Real":
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx - 1] + 1e-6),
                                      "u": simplify(sub_evaluations[node_idx] - (1e-6))}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(
                            model.mkTerm(Kind.ADD, sub_api_terms[node_idx - 1], model.mkReal(1, 100000))),
                                      "u": model.getValue(
                                          model.mkTerm(Kind.SUB, sub_api_terms[node_idx], model.mkReal(1, 100000)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx - 1] + 1e-6, "u": sub_evaluations[node_idx] - 1e-6}
                else:
                    if solver == "z3":
                        constraint = {"l": simplify(sub_evaluations[node_idx - 1] + 1),
                                      "u": simplify(sub_evaluations[node_idx] - (1))}
                    elif solver == "cvc":
                        constraint = {"l": model.getValue(
                            model.mkTerm(Kind.ADD, sub_api_terms[node_idx - 1], model.mkInteger(1))),
                                      "u": model.getValue(
                                          model.mkTerm(Kind.SUB, sub_api_terms[node_idx], model.mkInteger(1)))}
                    else:
                        constraint = {"l": sub_evaluations[node_idx - 1] + interval(1.0),
                                      "u": sub_evaluations[node_idx] - interval(1)}
    else:
        pass
    return constraint


def get_real_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, solver,
                        model):
    constraint = {"l": cur_eval, "u": cur_eval}

    if parent_op == "/":
        if solver == "z3":
            if node_idx == 0:
                tmp_eval = sub_evaluations[0]
                for idx in range(1, len(sub_evaluations)):
                    tmp_eval = simplify(tmp_eval * sub_evaluations[idx])
                sub_eval = simplify(tmp_eval)
                if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                    constraint["l"] = parent_cond["l"]
                else:
                    constraint["l"] = simplify(parent_cond["l"] * sub_eval)

                if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                    constraint["u"] = parent_cond["u"]
                else:
                    constraint["u"] = simplify(parent_cond["u"] * sub_eval)
            else:
                tmp_eval = sub_evaluations[0]
                for idx in range(1, len(sub_evaluations)):
                    tmp_eval = simplify(tmp_eval / sub_evaluations[idx])
                sub_eval = simplify(tmp_eval)
                if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                    constraint["l"] = parent_cond["l"]
                else:
                    constraint["l"] = simplify(sub_eval / parent_cond["l"])

                if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                    constraint["u"] = parent_cond["u"]
                else:
                    constraint["u"] = simplify(sub_eval / parent_cond["u"])
        elif solver == "cvc":
            if node_idx == 0:
                tmp_eval = sub_api_terms[0]
                for idx in range(1, len(sub_api_terms)):
                    tmp_eval = model.mkTerm(Kind.MULT, tmp_eval, sub_api_terms[idx])

                if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                    constraint["l"] = parent_cond["l"]
                else:
                    res = model.getValue(model.mkTerm(Kind.MULT, parent_cond["l"], tmp_eval))
                    constraint["l"] = res

                if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                    constraint["u"] = parent_cond["u"]
                else:
                    res = model.getValue(model.mkTerm(Kind.MULT, parent_cond["u"], tmp_eval))
                    constraint["u"] = res
            else:
                tmp_eval = sub_api_terms[0]
                for idx in range(1, len(sub_api_terms)):
                    tmp_eval = model.mkTerm(Kind.DIVISION, tmp_eval, sub_api_terms[idx])

                if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                    constraint["l"] = parent_cond["l"]
                else:
                    res = model.getValue(model.mkTerm(Kind.DIVISION, tmp_eval, parent_cond["l"]))
                    constraint["l"] = res

                if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                    constraint["u"] = parent_cond["u"]
                else:
                    res = model.getValue(model.mkTerm(Kind.DIVISION, tmp_eval, parent_cond["u"]))
                    constraint["u"] = res
        else:
            pass
    elif parent_op == "to_real":
        pass
    else:
        pass
    return constraint


def get_int_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, solver,
                       model):
    constraint = {"l": cur_eval, "u": cur_eval}
    return constraint


def get_arith_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, solver,
                         model):
    constraint = {"l": cur_eval, "u": cur_eval}
    if parent_op == "*":
        if solver == "z3":

            tmp_eval = sub_evaluations[0]
            for idx in range(1, len(sub_evaluations)):
                tmp_eval = simplify(tmp_eval * sub_evaluations[idx])

            sub_eval = simplify(tmp_eval)

            if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                constraint["l"] = parent_cond["l"]
            else:
                constraint["l"] = simplify(parent_cond["l"] / sub_eval)

            if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                constraint["u"] = parent_cond["u"]
            else:
                constraint["u"] = simplify(parent_cond["u"] / sub_eval)
        elif solver == "cvc":
            tmp_eval = sub_api_terms[0]
            for idx in range(1, len(sub_api_terms)):
                tmp_eval = model.mkTerm(Kind.MULT, tmp_eval, sub_api_terms[idx])

            if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                constraint["l"] = parent_cond["l"]
            else:
                res = model.getValue(model.mkTerm(Kind.DIVISION, parent_cond["l"], tmp_eval))
                constraint["l"] = res

            if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                constraint["u"] = parent_cond["u"]
            else:
                res = model.getValue(model.mkTerm(Kind.DIVISION, parent_cond["u"], tmp_eval))
                constraint["u"] = res
        else:
            pass
    elif parent_op == "+":
        if solver == "z3":
            tmp_eval = sub_evaluations[0]
            for idx in range(1, len(sub_evaluations)):
                tmp_eval = simplify(tmp_eval + sub_evaluations[idx])
            sub_eval = simplify(tmp_eval)

            if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                constraint["l"] = parent_cond["l"]
            else:
                constraint["l"] = simplify(parent_cond["l"] - sub_eval)

            if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                constraint["u"] = parent_cond["u"]
            else:
                constraint["u"] = simplify(parent_cond["u"] - sub_eval)
        elif solver == "cvc":
            tmp_eval = sub_api_terms[0]
            for idx in range(1, len(sub_api_terms)):
                tmp_eval = model.mkTerm(Kind.ADD, tmp_eval, sub_api_terms[idx])

            if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                constraint["l"] = parent_cond["l"]
            else:
                res = model.getValue(model.mkTerm(Kind.SUB, parent_cond["l"], tmp_eval))
                constraint["l"] = res

            if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                constraint["u"] = parent_cond["u"]
            else:
                res = model.getValue(model.mkTerm(Kind.SUB, parent_cond["u"], tmp_eval))
                constraint["u"] = res
        else:
            pass
    elif parent_op == "-":
        if len(sub_evaluations) == 0:
            if solver == "z3":
                constraint["u"] = -parent_cond["l"]
                constraint["l"] = -parent_cond["u"]
            elif solver == "cvc":
                if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                    constraint["u"] = -parent_cond["l"]
                else:
                    res = model.getValue(model.mkTerm(Kind.NEG, parent_cond["l"]))
                    constraint["u"] = res

                if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                    constraint["l"] = -parent_cond["u"]
                else:
                    res = model.getValue(model.mkTerm(Kind.NEG, parent_cond["u"]))
                    constraint["l"] = res
            else:
                constraint = {"l": parent_cond["u"] * (-1), "u": parent_cond["l"] * (-1)}
        else:
            if solver == "z3":
                if node_idx == 0:
                    tmp_eval = sub_evaluations[0]
                    for idx in range(1, len(sub_evaluations)):
                        tmp_eval = simplify(tmp_eval + sub_evaluations[idx])
                    sub_eval = simplify(tmp_eval)
                    if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                        constraint["l"] = parent_cond["l"]
                    else:
                        constraint["l"] = simplify(parent_cond["l"] + sub_eval)

                    if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                        constraint["u"] = parent_cond["u"]
                    else:
                        constraint["u"] = simplify(parent_cond["u"] + sub_eval)
                else:
                    tmp_eval = sub_evaluations[0]
                    for idx in range(1, len(sub_evaluations)):
                        tmp_eval = simplify(tmp_eval - sub_evaluations[idx])
                    sub_eval = simplify(tmp_eval)
                    if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                        constraint["u"] = -parent_cond["l"]
                    else:
                        constraint["u"] = simplify(sub_eval - parent_cond["l"])

                    if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                        constraint["l"] = -parent_cond["u"]
                    else:
                        constraint["l"] = simplify(sub_eval - parent_cond["u"])
            elif solver == "cvc":
                if node_idx == 0:
                    tmp_eval = sub_api_terms[0]
                    for idx in range(1, len(sub_api_terms)):
                        tmp_eval = model.mkTerm(Kind.ADD, tmp_eval, sub_api_terms[idx])

                    if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                        constraint["l"] = parent_cond["l"]
                    else:
                        res = model.getValue(model.mkTerm(Kind.ADD, parent_cond["l"], tmp_eval))
                        constraint["l"] = res

                    if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                        constraint["u"] = parent_cond["u"]
                    else:
                        res = model.getValue(model.mkTerm(Kind.ADD, parent_cond["u"], tmp_eval))
                        constraint["u"] = res
                else:
                    tmp_eval = sub_api_terms[0]
                    for idx in range(1, len(sub_api_terms)):
                        tmp_eval = model.mkTerm(Kind.SUB, tmp_eval, sub_api_terms[idx])

                    if parent_cond["l"].__class__.__name__ == "float" and parent_cond["l"] in [-inf, inf]:
                        constraint["l"] = parent_cond["l"]
                    else:
                        res = model.getValue(model.mkTerm(Kind.SUB, tmp_eval, parent_cond["l"]))
                        constraint["l"] = res

                    if parent_cond["u"].__class__.__name__ == "float" and parent_cond["u"] in [-inf, inf]:
                        constraint["u"] = parent_cond["u"]
                    else:
                        res = model.getValue(model.mkTerm(Kind.SUB, tmp_eval, parent_cond["u"]))
                        constraint["u"] = res
            else:
                pass
    else:
        pass

    return constraint


def get_string_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, solver,
                          model):
    if cur_eval.__class__.__name__ == "IntNumRef" or str(cur_eval)[0] != '"':
        return {"l": cur_eval, "u": cur_eval}

    constraint = cur_eval
    return constraint


def get_regp_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, solver,
                        model):
    if cur_eval.__class__.__name__ == "IntNumRef":
        return {"l": cur_eval, "u": cur_eval}

    constraint = cur_eval
    return constraint
