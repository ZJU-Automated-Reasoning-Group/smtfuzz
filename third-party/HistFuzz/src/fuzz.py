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


from genericpath import exists
import os
import random
import shutil
import time
import traceback
from copy import deepcopy

from src.building_blocks import BuggySeed, rename_variable_in_a_file, rule
from src.parsing.Ast import DeclareFun
from src.skeleton import Skeleton, obtain_hole, obtain_local_domain
from src.solver_run.solver import solver_runner
from src.utils.file_operation import export_smt2


def fuzz(skeleton_path, solver1, solver2, solver1_path, solver2_path, timeout, incremental, core, add_option_flag, rules, buggy, temp, argument, mutant=None, tactic=None):
    associate_rule = rule(rules)
    skeleton_obj = Skeleton(skeleton_path)
    initial_skeletons = skeleton_obj.skeleton_list
    dynamic_list = deepcopy(initial_skeletons)
    buggy_corpus = BuggySeed(buggy)
    file_count = 0
    bug_count = 0
    temp_dir = temp
    temp_core_dir = temp_dir + "/scripts/core" + str(core)
    if os.path.exists(temp_core_dir):
        shutil.rmtree(temp_core_dir)
    os.makedirs(temp_core_dir)
    start_time = time.time()
    total_count = 0
    theory = random.choice(["int", "real", "string", "bv", "fp", "array"])
    sort_list = []
    type_expr, expr_type, expr_var, seed_sort, seed_func = None, None, None, None, None
    while True:
        # print(seed)
        try:
            if incremental == "random":
                incremental_mode = random.choice(["incremental", "non-incremental"])
            else:
                incremental_mode = incremental
            skeleton_list, dynamic_list = skeleton_obj.choose_skeleton_and_remove(dynamic_list, incremental_mode)
            if theory == "real":
                buggy_typ_expr = buggy_corpus.real_formula
                buggy_expr_typ = buggy_corpus.real_formula_type
                buggy_expr_var = buggy_corpus.real_var
                buggy_expr_sort = buggy_corpus.real_formula_sort
                buggy_expr_func = buggy_corpus.real_formula_func
            elif theory == "int":
                buggy_typ_expr = buggy_corpus.int_formula
                buggy_expr_typ = buggy_corpus.int_formula_type
                buggy_expr_var = buggy_corpus.int_var
                buggy_expr_sort = buggy_corpus.int_formula_sort
                buggy_expr_func = buggy_corpus.int_formula_func
            elif theory == "string":
                buggy_typ_expr = buggy_corpus.string_formula
                buggy_expr_typ = buggy_corpus.string_formula_type
                buggy_expr_var = buggy_corpus.string_var
                buggy_expr_sort = buggy_corpus.string_formula_sort
                buggy_expr_func = buggy_corpus.string_formula_func
            elif theory == "bv":
                buggy_typ_expr = buggy_corpus.bv_formula
                buggy_expr_typ = buggy_corpus.bv_formula_type
                buggy_expr_var = buggy_corpus.bv_var
                buggy_expr_sort = buggy_corpus.bv_formula_sort
                buggy_expr_func = buggy_corpus.bv_formula_func
            elif theory == "fp":
                buggy_typ_expr = buggy_corpus.fp_formula
                buggy_expr_typ = buggy_corpus.fp_formula_type
                buggy_expr_var = buggy_corpus.fp_var
                buggy_expr_sort = buggy_corpus.fp_formula_sort
                buggy_expr_func = buggy_corpus.fp_formula_func
            elif theory == "array":
                buggy_typ_expr = buggy_corpus.array_formula
                buggy_expr_typ = buggy_corpus.array_formula_type
                buggy_expr_var = buggy_corpus.array_var
                buggy_expr_sort = buggy_corpus.array_formula_sort
                buggy_expr_func = buggy_corpus.array_formula_func
            new_ast, ast_var, _, func_list = construct_formula(skeleton_list, type_expr, expr_type, expr_var,
                                                               buggy_typ_expr, buggy_expr_typ, buggy_expr_var,
                                                               buggy_expr_sort, buggy_expr_func, associate_rule)

            if new_ast is not None:
                # sort_list += seed_sort
                if isinstance(func_list, list) and isinstance(seed_func, list):
                    func_list += seed_func
                new_formula = construct_scripts(new_ast, ast_var, sort_list, func_list, incremental_mode, argument)
                smt_file = export_smt2(new_formula, temp_core_dir, file_count)
                if smt_file is not None:
                    bug_flag = solver_runner(solver1_path, solver2_path, smt_file, timeout, incremental_mode,
                                             solver1, solver2, theory, add_option_flag, temp, tactic)
                    file_count += 1
                    total_count += 1
                    if bug_flag:
                        bug_count += 1
                    if time.time() - start_time > 10:
                        start_time = time.time()
                        if bug_count == 1 or bug_count == 0:
                            print(str(total_count) + " test instances solved  |  " + str(bug_count) + " bug found")
                        else:
                            print(str(total_count) + " test instances solved  |  " + str(bug_count) + " bugs found")
                    
                if file_count > 1000:
                    shutil.rmtree(temp_core_dir)
                    file_count = 0
                    if mutant is not None:
                        return

            if dynamic_list is None:
                theory = random.choice(["int", "real", "string", "bv", "fp", "array"])
                sort_list = []
                type_expr, expr_type, expr_var, seed_sort, seed_func = None, None, None, None, None
                dynamic_list = deepcopy(initial_skeletons)
        except (KeyboardInterrupt, SystemExit):
            print("bye!")
            break
        except Exception:
            traceback.print_exc()
            with open("exception.txt", "a") as e:
                e.write(traceback.format_exc())
            time.sleep(1)
            dynamic_list = deepcopy(initial_skeletons)


def exist_association(abstract_set: set, rules: rule, seed_type_formula: dict, buggy_type_formula: dict) -> list or None:
    """
    Check for the existence of association between abstract_set and candidate list.

    :param abstract_set: A set of abstract elements to check for association.
    :param rules: Association rule object.
    :param seed_type_formula: A dictionary containing type-formula mappings for seed elements.
    :param buggy_type_formula: A dictionary containing type-formula mappings for buggy elements.
    :return: A list of candidate elements meeting the association list, or None if no candidates found.
    """
    candidate_list = []

    if len(abstract_set) > 0:
        for keys in rules.rule_dic.keys():
            exist_association_flag = True

            # Split keys by delimiter (", ") to handle multiple elements
            if ", " in keys:
                k = keys.split(", ")
                for single in k:
                    if single not in abstract_set:
                        exist_association_flag = False
            else:
                if keys not in abstract_set:
                    exist_association_flag = False

            if exist_association_flag:
                k = rules.rule_dic[keys]

                # Split k by delimiter (", ") to handle multiple formulas
                if ", " in k:
                    formula_format = k.split(", ")
                else:
                    formula_format = [k]

                for single_format in formula_format:
                    candidate = seed_type_formula.get(single_format, None)
                    if candidate is None:
                        candidate = buggy_type_formula.get(single_format, None)
                        if candidate is not None:
                            candidate_list += candidate
                    else:
                        candidate_list += candidate

        if len(candidate_list) > 0:
            return candidate_list

    return None



def construct_formula(skeleton, seed_type_expr, seed_expr_type, seed_var, bug_type_formula, bug_formula_typ,
                      bug_formula_var, bug_formula_sort, bug_formula_func, bug_association):
    sort_list = list()
    func_list = list()
    ast_lists = list()
    var_lists = list()
    abstract_set = set()
    if seed_type_expr is None:
        seed_type_expr = dict()
        seed_expr_type = dict()
    if seed_var is None:
        seed_var = dict()
    if skeleton is not None:
        for ske in skeleton:
            local_var = list()
            blanks = obtain_hole(ske)
            local_domain = obtain_local_domain(ske)
            hole_replacer_dic = dict()
            assertion = str(ske)
            while len(blanks) > 0:
                blank = random.choice(blanks)
                # for blank in blanks:
                candidate = exist_association(abstract_set, bug_association, seed_type_expr, bug_type_formula)
                if candidate is not None:
                    replacer = random.choice(candidate)
                    abstract_set = set()
                    if bug_formula_var.get(replacer, False):
                        single_hole_var = bug_formula_var[replacer]
                        sort_list += bug_formula_sort.get(replacer, [])
                        func_list += bug_formula_func.get(replacer, [])
                    elif seed_var.get(replacer, False):
                        # pass
                        single_hole_var = seed_var[replacer]
                    else:
                        continue
                else:
                    replacer_type = random.choice(["seed", "seed", "seed", "buggy"])
                    if replacer_type == "seed" and len(list(seed_var.keys())) > 0:
                        replacer = random.choice(list(seed_var.keys()))
                        single_hole_var = seed_var[replacer]
                        if seed_expr_type[replacer] in bug_association.rule_set:
                            abstract_set.add(seed_expr_type[replacer])
                    else:
                        replacer = random.choice(list(bug_formula_var.keys()))
                        single_hole_var = bug_formula_var[replacer]
                        sort_list += bug_formula_sort.get(replacer, [])
                        func_list += bug_formula_func.get(replacer, [])
                        if bug_formula_typ[replacer] in bug_association.rule_set:
                            abstract_set.add(bug_formula_typ[replacer])
                assertion = assertion.replace(str(blank), replacer)
                hole_replacer_dic[str(blank)] = single_hole_var
                local_var += single_hole_var
                blanks.remove(blank)
                # terms, typ = get_subterms(replacer)
            if local_domain:
                for local in local_domain.keys():
                    single_local_var = local.split(" ")
                    candidate_var = []
                    for hole in local_domain[local]:
                        candidate_var += hole_replacer_dic[hole]
                    for var in single_local_var:
                        if var != "":
                            replacee = var + " " + var.replace("VAR", "TYPE")
                            if len(candidate_var) > 0:
                                replace_local_var = random.choice(candidate_var).split(", ")
                                if random.choice([True, False]):
                                    replace_format = replace_local_var[0].upper() + " " + replace_local_var[1]
                                else:
                                    replace_format = replace_local_var[0] + " " + replace_local_var[1]
                                assertion = assertion.replace(replacee, replace_format)
                            else:
                                assertion = assertion.replace(replacee, var + " " + "Bool")
            var_lists += local_var
            var_lists = list(set(var_lists))
            ast_lists.append(assertion)
        return ast_lists, var_lists, list(set(sort_list)), list(set(func_list))
    else:
        return None, None, None, None


def variable_translocation(ast, ast_var: dict):
    """
    Randomly replace variables in an SMT formula with other variables of the same type.

    Args:
        ast (list): List of strings representing the SMT formula.
        ast_var (dict): Dictionary containing variable names as keys and their types as values.

    Returns:
        list: List of strings representing the modified SMT formula.
    """
    if ast_var:
        replace_time = random.randint(1, 10)
        while replace_time > 0:
            replace_type = random.choice(list(ast_var.keys()))
            replace_ast_index = random.randint(0, len(ast) - 1)
            for var in ast_var[replace_type]:
                # Check if variable exists in the dict
                if " " + var + " " in ast[replace_ast_index] or " " + var + ")" in ast[replace_ast_index]:
                    # Replace variable in the dict with another variable of the same type
                    if " " + var + " " in ast[replace_ast_index]:
                        ast[replace_ast_index] = ast[replace_ast_index].replace(" " + var + " ", " " + random.choice(
                            ast_var[replace_type]) + " ", 1)
                        replace_time -= 1
                    if " " + var + ")" in ast[replace_ast_index]:
                        ast[replace_ast_index] = ast[replace_ast_index].replace(" " + var + ")", " " + random.choice(
                            ast_var[replace_type]) + ")", 1)
                        replace_time -= 1
                    break
    return ast




def construct_scripts(ast, var_list, sort, func, incremental, argument):
    """
    Construct scripts for SMT solver.

    :param ast: Assert of an SMT formula.
    :param var_list: List of variables in the SMT formula.
    :param sort: List of sort declarations.
    :param func: List of function declarations.
    :param incremental: Incremental mode flag.
    :return: The constructed script as a string.
    """
    formula = list()  # Initialize list for formulas
    type_var = {}  # Initialize dictionary for variable types

    # Add sort and function declarations to the formula list
    for i, s in enumerate(sort):
        sort[i] = s.replace("\n", "")
    formula += list(set(sort))
    for i, f in enumerate(func):
        func[i] = f.replace(";", "")
    formula += list(set(func))

    # Add variable declarations to the formula list
    if len(var_list) > 0:
        for v in var_list:
            name = v.split(", ")[0]
            typ = v.split(", ")[1]
            type_var.setdefault(typ, []).append(name)
            formula.append(str(DeclareFun(name, '', typ)))

    # Perform variable translocation
    ast = variable_translocation(ast, type_var)

    # Add push and pop commands for incremental mode
    if incremental == "incremental":
        ast = insert_push_and_pop(ast)
    else:
        ast.append("(check-sat)")

    # Combine all formulas
    formula = formula + ast

    # Construct script as a string
    s = "(set-logic ALL)\n"
    for content in formula:
        s = s + content + "\n"

    return s


def insert_push_and_pop(ast_list):
    """
    Adds "push" and "pop" commands to an SMT instance.

    :param ast_list: a list of SMT instance elements
    :return: a new list of SMT instance elements with "push" and "pop" commands added
    """
    ast_stack = 0
    new_ast = []
    left_count = len(ast_list)
    while left_count > 0:
        # Set the number of "push" commands to add based on how many elements are left in the list
        if left_count > 2:
            push_count = random.randint(1, 3)
        else:
            push_count = left_count
        left_count -= push_count
        # Add the "push" command with the number of elements to push
        new_ast.append("(push " + str(push_count) + ")")
        ast_stack += push_count
        # Add the elements to be pushed
        for i in range(push_count):
            new_ast.append(ast_list.pop())
        # Add the "check-sat" command
        new_ast.append("(check-sat)")
        # Set the number of "pop" commands to add based on the current stack size
        pop_count = random.randint(1, ast_stack)
        ast_stack -= pop_count
        # Add the "pop" command with the number of elements to pop
        new_ast.append("(pop " + str(pop_count) + ")")
    return new_ast


def collect_sort(file):
    """
    Collects the sort definitions in an SMT file.

    :param file: the path of the SMT file.
    :return: a list of lines that define sorts.
    """
    sort_list = []
    with open(file, "r") as smt_file:
        content = smt_file.readlines()
        for line in content:
            # Check if the line declares or defines a sort.
            if "declare-sort" in line or "define-sort" in line:
                sort_list.append(line)
    return sort_list

