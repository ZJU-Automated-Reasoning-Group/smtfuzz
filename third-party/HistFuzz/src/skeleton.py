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


import random

from src.parsing.Ast import Term, Expr
from src.parsing.Parse import parse_file
from src.parsing.Types import (
    NOT, AND, IMPLIES, OR, XOR, IFF
)
from src.utils.file_operation import get_smt_files_list


def process_seed(seed):
    script, glob = parse_file(seed, silent=True)
    return script, glob


def has_let(seed):
    file = open(seed, "r")
    content = file.readlines()
    for line in content:
        if "let " in line:
            return True
    return False


def get_subterms(expr):
    """
    Get all subexpression of term object expr.
    :returns: av_expr list of expressions
              expr_types list of types
              (s.t. expression e = av_expr[i] has type expr_types[i])
    """
    av_expr = []
    expr_types = []
    if isinstance(expr, Term):
        if expr.subterms:
            for s in expr.subterms:
                new_av, new_type = get_subterms(s)
                av_expr += new_av
                expr_types += new_type
            new_type = expr.type
            expr_types.append(new_type)
            av_expr.append(expr)
        else:
            av_expr.append(expr)
            expr_types.append(expr.type)
    elif type(expr) != str:
        if expr.term:
            new_av, new_type = get_subterms(expr.term)
            av_expr += new_av
            expr_types += new_type
    return av_expr, expr_types


def get_basic_subterms(expr, index, rename_flag=False):
    """
    Get all basic subexpression of term object expr.
    :param expr: a term object representing an SMT formula
    :param index: an integer representing the number of the assert containing the expression
    :param rename_flag: a boolean flag indicating whether to rename quantified variables
    :return: a list of term objects representing basic subexpressions of the input formula, 
    and a list of types representing the types of the corresponding basic subexpressions
    """
    basic_expr = []
    expr_types = []
    if isinstance(expr, Term):
        if expr.op in [NOT, AND, IMPLIES, OR, XOR, IFF] or expr.quantifier is not None or expr.let_terms is not None:
            if expr.quantifier is not None and rename_flag:
                # Rename quantified variables if rename_flag is True
                for v in range(len(expr.quantified_vars[0])):
                    expr.quantified_vars[0][v] = 'VAR' + str(v)
                for t in range(len(expr.quantified_vars[1])):
                    expr.quantified_vars[1][t] = 'TYPE' + str(t)
            # Recursively get basic subexpressions for the subterms of expr
            for s in expr.subterms:
                new_av, new_type = get_basic_subterms(s, index, rename_flag)
                basic_expr += new_av
                expr_types += expr_types
        else:
            # This is a basic subexpression, so add it to the list
            basic_expr.append([expr, index])
            expr_types.append(expr.type)
    elif isinstance(expr, str):
        pass
        # This is not a term object, so do nothing
    else:
        # This is a let-binding expression, so get basic subexpressions for its term
        if expr.term:
            new_av, new_type = get_basic_subterms(expr.term, index, rename_flag)
            basic_expr += new_av
            expr_types += new_type
    return basic_expr, expr_types



def get_all_basic_subformula(formula, rename_flag=False):
    """
    basic subformulas represent those formulas that don't contain any logical connectives
    :param rename_flag:
    :param formula:
    :return: a list of basic_subformula
    """
    basic_expr = list()
    for i in range(len(formula.assert_cmd)):
        exps, typ = get_basic_subterms(formula.assert_cmd[i], i, rename_flag)
        basic_expr += exps
    return basic_expr


def construct_skeleton(seed, flag=False):
    """
    Dig holes in the formula
    :param flag:
    :param seed:
    :return:
    """
    s, g = process_seed(seed)
    if s is None:
        pass
    else:
        index = [0] * len(s.assert_cmd)
        basic_formula = get_all_basic_subformula(s, flag)
        for i in range(len(basic_formula)):
            basic_formula[i][0].substitute(basic_formula[i][0],
                                           Expr(op="hole " + str(index[basic_formula[i][1]]), subterms=[]))
            index[basic_formula[i][1]] += 1
    return s


def extract_skeleton(seed, skeleton_dic):
    """
    extract the skeletons from a seed and add them to dict
    :param seed:
    :param skeleton_dic:
    :return:
    """
    s = construct_skeleton(seed, flag=True)
    if s is not None:
        for i in range(len(s.assert_cmd)):
            skeleton = str(s.assert_cmd[i])
            if "let " not in skeleton:
                if skeleton_dic.get(skeleton) is None:
                    skeleton_dic[skeleton] = 1
                else:
                    count = skeleton_dic[skeleton]
                    skeleton_dic[skeleton] = count + 1
    return skeleton_dic
    # print(str(s.assert_cmd[i].term))


def export_skeleton(formula_path, skeleton_file):
    skeleton_dic = dict()
    files = get_smt_files_list(formula_path)
    for file in files:
        skeleton_dic = extract_skeleton(file, skeleton_dic)
    # skeleton_order = sorted(skeleton_dic.items(), key=lambda x: x[1])
    # with open("skeleton_num.txt", "w") as fout:
    #     for ske in skeleton_order:
    #         fout.write(str(ske) + "\n")
    f1 = open(skeleton_file, "w")
    skeleton_list = list()
    for key in skeleton_dic.keys():
        # if key.count("hole") > 10:
        #     big_skeleton_list.append(key + "\n")
        # else:
        skeleton_list.append(key + "\n")
    f1.writelines(skeleton_list)
    f1.close()
    restruct_skeleton(skeleton_file)


def obtain_hole(skeleton):
    """

    :param skeleton: a ast that contains holes
    :return: a list of the holes the skeleton contain
    """
    hole_list = list()
    exprs, typ = get_basic_subterms(skeleton, 0)
    for hole in exprs:
        hole_list.append(hole[0])
    return hole_list


def obtain_local_domain(skeleton):
    local_domain = dict()
    initial_term = skeleton.term

    def recurrently_obtain_local(term, local_dic: dict):
        if isinstance(term, Term):
            if term.quantifier is not None:
                local_var = ""
                for v in term.quantified_vars[0]:
                    local_var += v + " "
                hole_list = list()
                for h in obtain_hole(term):
                    hole_list.append(str(h))
                if isinstance(local_var, str) and isinstance(local_dic, dict) and isinstance(hole_list, list):
                    local_dic[local_var] = hole_list
            if term.subterms is not None:
                for t in term.subterms:
                    local_dic = recurrently_obtain_local(t, local_dic)
            return local_dic

    return recurrently_obtain_local(initial_term, local_domain)


def obtain_skeleton_set(file_list):
    skeleton_set = set()
    for file in file_list:
        s = construct_skeleton(file, flag=True)
        if s is not None:
            for i in range(len(s.assert_cmd)):
                skeleton = str(s.assert_cmd[i])
                skeleton_set.add(skeleton)
    return skeleton_set


class Skeleton(object):
    def __init__(self, path_to_skeleton):
        self.script, self.global_var = parse_file(path_to_skeleton)
        self.skeleton_list = self.script.assert_cmd
        # self.SEED = random_seed
        # self.dynamic_skeleton_list = self.skeleton_list

    @staticmethod
    def random_choose_skeletons(skeleton_list):
        ast_count = 1
        ast_list = list()
        for i in range(ast_count):
            ast_list.append(random.choice(skeleton_list))
        return ast_list, ast_list

    @staticmethod
    def choose_skeleton_and_remove(skeleton_list, incremental):
        ast_list = list()
        if skeleton_list is not None and len(skeleton_list) > 5:
            ast_count = random.choice([1, 2, 3, 3, 4, 4, 5])
            if incremental == "incremental":
                ast_count = ast_count * random.choice([2, 3])
                if ast_count > len(skeleton_list):
                    ast_count = len(skeleton_list)
                if ast_count > 10:
                    ast_count = 10
            for i in range(ast_count):
                ast = random.choice(skeleton_list)
                ast_list.append(ast)
                skeleton_list.remove(ast)
            # return ast_list
        else:
            ast_list = skeleton_list
            skeleton_list = None

        return ast_list, skeleton_list


def restruct_skeleton(skeleton_path):
    new_content = []
    with open(skeleton_path, "r") as f:
        content = f.readlines()
    for line in content:
        index = 0
        local_count = dict()
        while line.count("VAR" + str(index) + " TYPE" + str(index)) > 0:
            if line.count("VAR" + str(index) + " TYPE" + str(index)) > 1:
                local_count["VAR" + str(index) + " TYPE" + str(index)] = line.count(
                    "VAR" + str(index) + " TYPE" + str(index))
            index += 1
        if len(list(local_count.keys())) > 0:
            # print(line)
            for k in local_count.keys():
                count = local_count[k]
                while count > 1:
                    line = line.replace(k, "VAR" + str(index) + " TYPE" + str(index), 1)
                    count -= 1
                    index += 1
            # print(line)
        new_content.append(line)
    with open(skeleton_path, "w") as f1:
        f1.writelines(new_content)
