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


import os
import random
import re
import shutil
import string
from copy import deepcopy

from src.parsing.Ast import Var, Assert, Term, Const, Expr
from src.parsing.TimeoutDecorator import exit_after
from src.parsing.Types import TYPES, FP_TYPE, BITVECTOR_TYPE, ARRAY_TYPE
from src.skeleton import get_all_basic_subformula, process_seed, get_subterms
from src.utils.file_operation import get_all_smt2_file, get_txt_files_list
from src.utils.type import return_type


def classify_formula(path_list):
    """
    copy the formulas to different directory according to the variable type each formula contain
    :param path1: source path
    :return:
    """
    file_list = []
    for path in path_list:
        file_list += get_all_smt2_file(path)
    int_list, real_list, string_list, bv_list, fp_list, array_list = [], [], [], [], [], []
    for file in file_list:
        flag = True
        if check_sort_func(file):
            with open(file, "r") as f:
                content = f.read()
            if "Real" in content:
                flag = False
                real_list.append(file)
            if "BitVec" in content or "_ bv" in content:
                flag = False
                bv_list.append(file)
            if "Int" in content:
                flag = False
                int_list.append(file)
            if "String" in content or "re." in content:
                flag = False
                string_list.append(file)
            if "Array" in content:
                flag = False
                array_list.append(file)
            if "Float" in content or "fp" in content:
                flag = False
                fp_list.append(file)
            if flag:
                pass
    return int_list, real_list, string_list, bv_list, fp_list, array_list


def collect_basic_building_blocks(path_list_1, path_list_2=None, path_list_3=None):
    """
    collect basic building blocks to construct new formulas
    :param path_list_1:
    :param path_list_2: Alternative path list
    :param path_list_3: Alternative path list
    :return: a list contain basic alternative
    """
    path_list = path_list_1
    if path_list_2 is not None:
        path_list = path_list + path_list_2
    if path_list_3 is not None:
        path_list = path_list + path_list_3
    random.shuffle(path_list)
    seed_count = random.randint(2, 5)
    building_blocks_list = list()
    block_id_list = list()  # belong to which formula
    for j, file in enumerate(path_list):
        scripts, var = process_seed(file)
        if scripts is not None:
            for term in get_all_basic_subformula(scripts):
                building_blocks_list.append(term[0])
                block_id_list.append(j)
            if j == seed_count:
                break
    return building_blocks_list, block_id_list


class BuildingBlocks(object):
    def __init__(self, path_to_file):
        self.scripts, self.global_vars = process_seed(path_to_file)
        self.building_block_list = list()
        self.building_block_var = dict()
        self.building_block_const = dict()
        self.all_variables = list()
        self.basic_formula_tuple = tuple()
        self.abstract_formula_dic = dict()
        self.sort_list = list()
        self.func_list = list()

        if self.scripts is not None:
            self._collect_building_blocks()
            self._building_block_variable()
            self.basic_formula_tuple = self._abstract_formula()
            with open(path_to_file, "r") as f:
                content = f.readlines()
            for line in content:
                if "declare-sort" in line or "define-sort" in line:
                    self.sort_list.append(line.replace("\n", ""))
                if re.search(r"\(define-fun", line) or re.search(r"\(declare-fun", line):
                    if re.search(r"\(\s*\)", line) or re.search(r"\(\n", line):
                        pass
                    else:
                        self.func_list.append(line.replace("\n", ""))

    def _collect_building_blocks(self):
        for term in get_all_basic_subformula(self.scripts):
            valid_flag = True
            new_term = term[0]
            terms, typ = get_subterms(new_term)
            for t in terms:
                if t.type == "Unknown":
                    valid_flag = False
            if valid_flag:
                self.building_block_list.append(new_term)

    def _building_block_variable(self):
        all_variable_list = list()
        for BB in self.building_block_list:
            var_list = list()
            const_list = list()
            valid_basic_block_flag = True
            subterms, typ = get_subterms(BB)
            for term in subterms:
                if term.is_var:
                    # print("var, ", term)
                    if term not in var_list:
                        var_list.append(term)
                    if [term, term.type] not in all_variable_list:
                        all_variable_list.append([term, term.type])
                if term.is_const:
                    if term not in const_list:
                        const_list.append(term)
            if valid_basic_block_flag:
                self.building_block_var[str(BB)] = var_list
                self.building_block_const[str(BB)] = const_list
        self.all_variables = all_variable_list

    def _abstract_formula(self):
        formula = tuple()
        for inx, origin_b in enumerate(self.building_block_list):
            try:
                if origin_b.is_var and len(self.building_block_var[str(origin_b)]) == 1:
                    var_this_round = deepcopy(self.building_block_var[str(origin_b)][0])
                    if "Array" in var_this_round.type:
                        block = Var("var_Array", var_this_round.type)
                    elif "FloatingPoint" in str(var_this_round.type):
                        block = Var("var_FloatingPoint", var_this_round.type)
                    elif "BitVec" in str(var_this_round.type):
                        block = Var("var_BitVec", var_this_round.type)
                    else:
                        block = Var("var_" + str(var_this_round.type), var_this_round.type)
                elif origin_b.is_const and len(self.building_block_const[str(origin_b)]) == 1:
                    const_this_round = deepcopy(self.building_block_const[str(origin_b)][0])
                    if "Array" in const_this_round.type:
                        block = Var("const_Array", const_this_round.type)
                    elif "FloatingPoint" in str(const_this_round.type):
                        block = Var("const_FloatingPoint", const_this_round.type)
                    elif "BitVec" in str(const_this_round.type):
                        block = Var("const_BitVec", const_this_round.type)
                    else:
                        block = Const(name="const_" + str(const_this_round.type), type=const_this_round.type)
                else:
                    block = deepcopy(origin_b)
                    for var in self.building_block_var[str(origin_b)]:
                        var_this_round = deepcopy(var)
                        # var_this_round = var
                        if "Array" in str(var_this_round.type):
                            block.substitute(var_this_round, Var("var_Array", var.type))
                        elif "FloatingPoint" in str(var_this_round.type):
                            block.substitute(var_this_round, Var("var_FloatingPoint", var.type))
                        elif "BitVec" in str(var_this_round.type):
                            block.substitute(var_this_round, Var("var_BitVec", var.type))
                        else:
                            block.substitute(var_this_round, Var("var_" + str(var.type), var.type))
                    for const in self.building_block_const[str(origin_b)]:
                        const_this_round = deepcopy(const)
                        # const_this_round = const
                        if "Array" in str(const_this_round.type):
                            new_const = Const(name="const_Array", type=const.type)
                            block.substitute(const_this_round, new_const)
                        elif "FloatingPoint" in str(const_this_round.type):
                            new_const = Const(name="const_FloatingPoint", type=const.type)
                            block.substitute(const_this_round, new_const)
                        elif "BitVec" in str(const_this_round.type):
                            new_const = Const(name="const_BitVec", type=const.type)
                            block.substitute(const_this_round, new_const)
                        else:
                            new_const = Const(name="const_" + str(const.type), type=const.type)
                            block.substitute(const_this_round, new_const)
                if block.subterms is not None:
                    for subterm in block.subterms:
                        if subterm.op is not None:
                            op = subterm.op
                            return_typ = return_type.get(op, None)
                            if return_typ is not None and return_typ != "Unknown":
                                if "var" in str(subterm):
                                    block.substitute(subterm, Expr(op="var_" + return_typ, subterms=[]))
                                else:
                                    block.substitute(subterm, Expr(op="const_" + return_typ, subterms=[]))
                            elif return_typ == "Unknown":
                                if op == "ite":
                                    if str(subterm.subterms[1]) == str(subterm.subterms[2]):
                                        name_token = str(subterm.subterms[1]).split("_")
                                        typ = name_token[1]
                                        block.substitute(subterm, Expr(op="var_" + typ, subterms=[]))
                                elif "Real" in str(subterm) and "var" in str(subterm):
                                    block.substitute(subterm, Expr(op="var_Real", subterms=[]))
                                elif "Real" in str(subterm) and "var" not in str(subterm):
                                    block.substitute(subterm, Expr(op="const_Real", subterms=[]))
                                elif "Real" not in str(subterm) and "var" in str(subterm):
                                    block.substitute(subterm, Expr(op="var_Int", subterms=[]))
                                elif "Real" not in str(subterm) and "var" not in str(subterm):
                                    block.substitute(subterm, Expr(op="const_Int", subterms=[]))
                regular_string = str(block).replace(" (", " ")
                regular_string = regular_string.replace(" )", " ")
                regular_string = regular_string.replace("  ", " ")
                regular_string = regular_string.replace("( ", "(")
                regular_string = regular_string.replace(" )", ")")
                self.abstract_formula_dic[inx] = regular_string
                formula = formula + (regular_string,)

            except Exception as e:
                pass
        return formula


def merge_file_and_rename_variable(file_path_list):
    index = 0
    BB_list = list()
    for file in file_path_list:
        single_list = list()
        building_blocks_object = BuildingBlocks(file)
        if building_blocks_object.scripts is not None:
            for var in building_blocks_object.all_variables:
                var_this_round = deepcopy(var[0])
                for ast in building_blocks_object.scripts.assert_cmd:
                    if isinstance(ast, Assert) and isinstance(ast.term, Term):
                        ast.term.substitute(var_this_round, Var("var" + str(index), var[1]))
                index += 1
        for idx, formula in enumerate(building_blocks_object.building_block_list):
            abstract = building_blocks_object.abstract_formula_dic.get(idx, "Null")
            single_list.append([abstract, formula, building_blocks_object.sort_list, building_blocks_object.func_list])
        BB_list += single_list
    return BB_list


def check_sort_func(file_path):
    try:
        with open(file_path, "r") as f:
            content = f.read()
        if "declare-sort" in content or "define-sort" in content or "(define-fun" in content or "datatype" in content:
            return False
        else:
            return True
    except UnicodeDecodeError:
        return False


def rename_variable_in_file(file):
    @exit_after(60)
    def rename_a_file(single_file):
        index = 0
        type_formula = dict()
        formula_type = dict()
        formula_var = dict()
        building_blocks_object = BuildingBlocks(single_file)
        if building_blocks_object.scripts is not None:
            for var in building_blocks_object.all_variables:
                var_this_round = deepcopy(var[0])
                for ast in building_blocks_object.scripts.assert_cmd:
                    if isinstance(ast, Assert) and isinstance(ast.term, Term):
                        ast.term.substitute(var_this_round, Var("extra_var" + str(index), var[1]))
                index += 1
        for idx, formula in enumerate(building_blocks_object.building_block_list):
            abstract = building_blocks_object.abstract_formula_dic.get(idx, "Null")
            if type_formula.get(abstract) is not None:
                type_formula[abstract].append(str(formula))
            else:
                type_formula[abstract] = [str(formula)]
            formula_type[str(formula)] = abstract
            var_list = []
            for v in building_block_variables(formula):
                var_list.append(str(v.name) + ", " + str(v.type))
            formula_var[str(formula)] = var_list
        return type_formula, formula_type, formula_var, building_blocks_object.sort_list, building_blocks_object.func_list

    return rename_a_file(file)


def rename_variable_in_a_file(file):
    type_expr, expr_type, expr_var, file_sort, file_func = None, None, None, None, None
    try:
        type_expr, expr_type, expr_var, file_sort, file_func = rename_variable_in_file(file)
    except KeyboardInterrupt:
        pass
    finally:
        return type_expr, expr_type, expr_var, file_sort, file_func


def export_basic_formula(formula_list, output):
    formula_list.sort(key=(lambda x: x[0]))
    with open(output, "w") as f:
        f.write("% var_Bool\nvar00; var00, Bool; \n% const_Bool\ntrue\nfalse")
        for i, formula in enumerate(formula_list):
            formula_str = str(formula[1])
            for index, fun in enumerate(formula[3]):
                signature = fun.split(" ")[1]
                formula_str = formula_str.replace("(" + signature + " ", "(bug" + str(i) + "_" + signature + " ")
            if formula[0] in ["var_Bool", "const_Bool"]:
                continue
            if i == 0 or formula_list[i - 1][0] != formula[0]:
                f.write("\n% " + formula[0] + "\n" + formula_str)
            else:
                f.write("\n" + formula_str)
            expr, typ = get_subterms(formula[1])
            for e in expr:
                if e.is_var:
                    f.write("; " + e.name + ", " + str(e.type) + "; ")
            if len(formula[2]) > 0:
                f.write("sort: ")
                for sort in formula[2]:
                    f.write(sort + "; ")
            if len(formula[3]) > 0:
                f.write("func: ")
                for func in formula[3]:
                    if "(declare-fun " in func:
                        f.write(func.replace("(declare-fun ", "(declare-fun bug" + str(i) + "_") + "; ")
                    elif "(define-fun " in func:
                        f.write(func.replace("(define-fun ", "(define-fun bug" + str(i) + "_") + "; ")



def building_block_variables(building_blocks):
    subterms, typ = get_subterms(building_blocks)
    var_list = list()
    for term in subterms:
        if term.is_var:
            if term.type is None:
                pass
            elif term not in var_list:
                var_list.append(term)
    return var_list


def generate_formula(abstract_set):
    """
    generate formulas according to association rules
    :param abstract_set:
    :return:
    """
    r = rule()
    candidates = list()
    generated_formula = list()
    inter_set = abstract_set.intersection(r.rule_set)
    for keys in r.rule_dic.keys():
        exist_flag = True
        if ", " in keys:
            k = keys.split(", ")
            for single in k:
                if single not in inter_set:
                    exist_flag = False
                    break
        else:
            if keys not in inter_set:
                exist_flag = False
        if exist_flag and r.rule_dic[keys] not in candidates:
            candidates.append(r.rule_dic[keys])
    # obtain candidate abstract formula (at least 5)
    while len(candidates) != 0 and len(generated_formula) < 5:
        for idx, candidate in enumerate(candidates):
            candidate = candidate.replace("(", "")
            candidate = candidate.replace(")", "")
            if ", " in candidate:
                for sub_idx, c in enumerate(candidate.split(", ")):
                    generated_formula.append(generate_term(c, str(idx) + "_" + str(sub_idx)))
            else:
                generated_formula.append(generate_term(candidate, str(idx)))
    return generated_formula


def generate_term(term_template: str, index: str):
    abstract_term = term_template.split(" ")
    term_list = []
    for i, atom in enumerate(abstract_term):
        if i == 0:
            op = atom
        else:
            sort = atom.split("_")
            if sort[0] == "var":
                term_list.append(Var(name="assoiciate" + index + "_var" + str(i), type=sort[1]))
            elif sort[0] == "const":
                if sort[1] == "Int":
                    term_list.append(Const(name=str(random.randint(0, 1000)), type="Int"))
                elif sort[1] == "Real":
                    number = str(random.randint(0, 1000)) + "." + str(random.randint(1, 999))
                    term_list.append(Const(name=number, type="Real"))
                elif sort[1] == "String":
                    s = "\""
                    s += "".join(
                        random.choice(string.ascii_letters + string.digits) for i in range(random.randint(1, 20)))
                    s += "\""
                    term_list.append(Const(name=s, type="String"))
    return Expr(op, term_list)


class rule(object):
    def __init__(self, rule_path):
        self.config_path = rule_path
        self.rule_dic = self._read_config()
        self.rule_set = self._key_set()

    def _read_config(self):
        rule_dict = dict()
        f = open(self.config_path, "r")
        rule_list = f.readlines()
        for line in rule_list:
            if ";" in line:
                rule_list.remove(line)
            else:
                line = line.replace("\n", "")
                line = line.replace("{", "")
                line = line.replace("}", "")
                # print(line)
                line = line.split(" (conf")[0]
                rule_pair = line.split(" -> ")
                rule_dict[rule_pair[0]] = rule_pair[1]
        return rule_dict

    def _key_set(self):
        k_set = set()
        for k in self.rule_dic.keys():
            if ", " in k:
                key_list = k.split(", ")
                for i in range(len(key_list)):
                    k_set.add(key_list[i])
            else:
                k_set.add(k)
        return k_set


class BuggySeed(object):
    def __init__(self, path):
        self.path = path
        self.int_formula = dict()
        self.int_formula_type = dict()
        self.int_var = dict()
        self.int_formula_sort = dict()
        self.int_formula_func = dict()
        self.real_formula = dict()
        self.real_formula_type = dict()
        self.real_var = dict()
        self.real_formula_sort = dict()
        self.real_formula_func = dict()
        self.string_formula = dict()
        self.string_formula_type = dict()
        self.string_var = dict()
        self.string_formula_sort = dict()
        self.string_formula_func = dict()
        self.bv_formula = dict()
        self.bv_formula_type = dict()
        self.bv_var = dict()
        self.bv_formula_sort = dict()
        self.bv_formula_func = dict()
        self.fp_formula = dict()
        self.fp_formula_type = dict()
        self.fp_var = dict()
        self.fp_formula_sort = dict()
        self.fp_formula_func = dict()
        self.array_formula = dict()
        self.array_formula_type = dict()
        self.array_var = dict()
        self.array_formula_sort = dict()
        self.array_formula_func = dict()
        self.read_corpus()

    def read_corpus(self):
        files = get_txt_files_list(self.path)
        for file in files:
            if "int.txt" in file:
                self.read_single_file(file, self.int_formula, self.int_formula_type, self.int_var, self.int_formula_sort
                                      , self.int_formula_func)
            elif "real.txt" in file:
                self.read_single_file(file, self.real_formula, self.real_formula_type, self.real_var,
                                      self.real_formula_sort, self.real_formula_func)
            elif "string.txt" in file:
                self.read_single_file(file, self.string_formula, self.string_formula_type, self.string_var,
                                      self.string_formula_sort, self.string_formula_func)
            elif "bv.txt" in file:
                self.read_single_file(file, self.bv_formula, self.bv_formula_type, self.bv_var, self.bv_formula_sort,
                                      self.bv_formula_func)
            elif "fp.txt" in file:
                self.read_single_file(file, self.fp_formula, self.fp_formula_type, self.fp_var, self.fp_formula_sort,
                                      self.fp_formula_func)
            elif "array.txt" in file:
                self.read_single_file(file, self.array_formula, self.array_formula_type, self.array_var,
                                      self.array_formula_sort, self.array_formula_func)

    @staticmethod
    def read_single_file(path, type_formula: dict, formula_type: dict, formula_var: dict, formula_sort: dict,
                         formula_func: dict):
        with open(path, "r") as f:
            file = f.readlines()
            typ = None
            formula = None
            func_line = ""
            sort_line = ""
            for line in file:
                line = line.replace("\n", "")
                if line == "":
                    pass
                elif line[0] == "%":
                    if formula is not None:
                        type_formula[typ] = formula
                    typ = line.replace("% ", "")
                    formula = []
                else:
                    if ";" in line:
                        content = line
                        if "func: " in line:
                            content = line.split("func: ")[0]
                            func_line = line.split("func: ")[1]
                        if "sort: " in line:
                            sort_line = content.split("sort: ")[1]
                            content = content.split("sort: ")[0]

                        content_list = content.split("; ")
                        for index, c in enumerate(content_list):
                            if ";" in c:
                                content_list[index] = c.replace(";", "")
                        while "" in content_list:
                            content_list.remove("")
                        formula.append(content_list[0])
                        formula_type[content_list[0]] = typ
                        formula_var[content_list[0]] = content_list[1:]
                        formula_func[content_list[0]] = func_line.split("; ")
                        formula_sort[content_list[0]] = sort_line.split("; ")
                    else:
                        formula.append(line)
                        formula_type[line] = typ
                        formula_var[line] = []


def simplify(file1):
    expr_set = set()
    with open(file1, "r") as f:
        content = f.readlines()
        for line in content:
            while content.count(line) > 1:
                content.remove(line)
            if ";" in line:
                line_pattern = line.split(";")[0]
            else:
                line_pattern = line
            var_list = list(set(re.findall(r'var\d+', line_pattern)))
            if len(var_list) > 0:
                for i, var in enumerate(var_list):
                    line_pattern = line_pattern.replace(var + " ", "var" + str(i) + " ")
                    line_pattern = line_pattern.replace(var + ")", "var" + str(i) + ")")
                    line_pattern = line_pattern.replace(var + ",", "var" + str(i) + ",")
            if line_pattern not in expr_set:
                expr_set.add(line_pattern)
            else:
                content.remove(line)
    with open(file1, "w") as f2:
        f2.writelines(content)


def export_buggy_seed(file_path, output_path):
    int_list, real_list, string_list, bv_list, fp_list, array_list = classify_formula([file_path])
    if os.path.exists(output_path):
        shutil.rmtree(output_path)
    os.makedirs(output_path)
    export_basic_formula(merge_file_and_rename_variable(bv_list), output_path + "/bv.txt")
    export_basic_formula(merge_file_and_rename_variable(fp_list), output_path + "/fp.txt")
    export_basic_formula(merge_file_and_rename_variable(int_list), output_path + "/int.txt")
    export_basic_formula(merge_file_and_rename_variable(real_list), output_path + "/real.txt")
    export_basic_formula(merge_file_and_rename_variable(string_list), output_path + "/string.txt")
    export_basic_formula(merge_file_and_rename_variable(array_list), output_path + "/array.txt")
    simplify(output_path + "/bv.txt")
    simplify(output_path + "/fp.txt")
    simplify(output_path + "/int.txt")
    simplify(output_path + "/real.txt")
    simplify(output_path + "/string.txt")
    simplify(output_path + "/array.txt")

