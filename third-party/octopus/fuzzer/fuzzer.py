import multiprocessing
import random
import operator
from utils.randomness import Randomness
from termcolor import colored
from runner.z3_python_api import check_satisfiability
from fuzzer.helper_functions import export_mutants, enrich_true_and_false_nodes, \
    pick_true_and_false_nodes_at_random, get_tree_depth
from parsing.Ast import DeclareConst, DeclareFun, DefineConst, DefineFun, DefineFunRec, DefineFunsRec, FunDecl
from z3 import *


def generate_mutants(smt_Object, path_to_directory, maxDepth, maxAssert, seed, theory, fuzzing_parameters, target=None, generation_flag=True, model_num=10):
    def generate_mutants_in_a_thread(smt_Object, path_to_directory, seed, theory, fuzzing_parameters, target=None, generation_flag=True, model_num=10):
        # We have to create a new randomness object here
        randomness = Randomness(seed)
        print("####### Generating mutants at location: " + colored(path_to_directory, "blue", attrs=["bold"]))
        print("####### Some stats: ")
        # print("\t\tNumber of assertions = " + colored(str(smt_Object.get_total_number_of_assertions()), "yellow", attrs=["bold"]))
        # print("\t\tNumber of assignments = " + colored(str(smt_Object.assign_num), "yellow", attrs=["bold"]))
        if len(smt_Object.op_occs) > 0:
            nodes, snippets, unsat_cores, maps = get_all_truth_values_in_astVector(smt_Object, randomness, theory, generation_flag, model_num)
            enrichment_steps = fuzzing_parameters["enrichment_steps"]
            number_of_mutants = fuzzing_parameters["number_of_mutants"]
            print("\t\tNumber of enrichment steps = " + colored(str(enrichment_steps), "yellow", attrs=["bold"]))
            print("\t\tNumber of mutants = " + colored(str(number_of_mutants), "yellow", attrs=["bold"]))
            print("\t\tMax Assert = " + colored(str(maxAssert), "yellow", attrs=["bold"]))
            print("\t\tMax Depth = " + colored(str(maxDepth), "yellow", attrs=["bold"]))
            print("####### Enriching the set of true and false nodes with more complex trees..")
            constructed_formulas = enrich_true_and_false_nodes(nodes, snippets, enrichment_steps, randomness, maxDepth)

            print("####### Generating the mutants by picking true and false nodes..")
            mutants, oracles = pick_true_and_false_nodes_at_random(constructed_formulas,
                                                                   number_of_mutants=number_of_mutants,
                                                                   max_assertions=maxAssert,
                                                                   randomness=randomness,
                                                                   unsat_core=unsat_cores,
                                                                   maps=maps,
                                                                   target=target)
            print("####### Exporting mutants..")
            export_mutants(mutants, oracles, path_to_directory)
            print("####### Done with exporting")
        else:
            print(colored("Nothing in TRUE or FALSE node. Nothing we can do here.", "red", attrs=["bold"]))

    process = multiprocessing.Process(target=generate_mutants_in_a_thread, args=(smt_Object,
                                                                                 path_to_directory,
                                                                                 seed,
                                                                                 theory,
                                                                                 fuzzing_parameters,
                                                                                 target, generation_flag, model_num))
    process.start()
    process.join(fuzzing_parameters["mutant_generation_timeout"])
    if process.is_alive():
        process.terminate()
        print(colored("TIMEOUT WHILE GENERATING MUTANTS", "red", attrs=["bold"]))
        return 1
    return 0


def get_com_model(com_ast):
    s = Solver()
    s.add(com_ast)
    satis = s.check()
    if satis == sat:
        model = s.model()
        if type(model) == bool:
            return False
        else:
            return model
    elif satis == unsat:
        return get_com_model(Not(com_ast))
    else:
        return False



def get_all_truth_values_in_astVector(smt_Object, randomness_object, theory, generation_flag, model_num=10):
    """
    Get truth values for all the leaves and sub-trees in the astVector
    """
    print("####### Evaluating truth values for all nodes..")
    
    # Generate models for the assertion
    models = []
    if len(smt_Object.op_occs) > model_num:
        candidates = random.sample(smt_Object.op_occs, model_num)
    else:
        candidates = smt_Object.op_occs

    for candidate in candidates:
        smt_string = complete_smt_instance(smt_Object, candidate)
        ast_vec = parse_smt2_string(smt_string)
        model = get_com_model(ast_vec[0])
        models.append(model)

    # Evaluate truth values of nodes in the assertion
    nodes = []
    snippets = []
    for term in smt_Object.op_occs:
        nodes.append(Node(complete_smt_instance(smt_Object, term)))


    # Obtain unsat cores
    unsat_cores, mapping = get_unsat_cores(nodes)

    for model in models:
        if model is not None:
            for node in nodes:
                if model.eval(node.node, model_completion=True):
                    node.truth_values.append(True)
                    node.model_count += 1
                elif not model.eval(node.node, model_completion=True):
                    node.truth_values.append(False)
                    node.model_count += 1
            if generation_flag:
                snippets.append(snippet_generation(model, randomness_object))
            else:
                snippets.append([])

    return nodes, snippets, unsat_cores, mapping


class Node:
    def __init__(self, term):
        self.vector = parse_smt2_string(term)
        self.truth_values = []
        self.model_count = 0
        if self.vector:
            self.node = self.vector[0]


def complete_smt_instance(script, subterm):
    # Generate a complete SMT instance with the given subterm
    init_script = ""
    for cmd in script.commands:
        if isinstance(cmd, DeclareConst) or isinstance(cmd, DeclareFun) or isinstance(cmd, DefineConst) or isinstance(
                cmd, DefineFun) or isinstance(cmd, DefineFunRec) or isinstance(cmd, DefineFunsRec) or isinstance(cmd,
                                                                                                                 FunDecl):
            init_script += str(cmd) + "\n"
    new_script = init_script + "(assert " + str(subterm) + ")\n(check-sat)\n"
    return new_script


def snippet_generation(assignment, randomness):
    # Helper function to identify the sort (type) of a variable
    def check_sort(v, list1, list2, list3, list4, list5):
        if v in list1:
            return 0
        if v in list2:
            return 1
        if v in list3:
            return 2
        if v in list4:
            return 3
        if v in list5:
            return 4

    # Helper function to build a snippet based on the sorts of the two input candidates
    def build_snippet(sort_idx1, sort_idx2, candidate1, candidate2, assignment):
        # Code for handling two integer candidates
        if sort_idx1 == 0 and sort_idx2 == 0:
            x = Int("%s" % candidate1)
            y = Int("%s" % candidate2)
            op1 = random.choice(int_op)
            op2 = random.choice(int_com)
            if op2 in [operator.lt, operator.gt]:
                return Not(op2(op1(x, y), op1(assignment[candidate1], assignment[candidate2])))
            else:
                return op2(op1(x, y), op1(assignment[candidate1], assignment[candidate2]))

        # Code for handling two real candidates
        elif sort_idx1 == 1 and sort_idx2 == 1:
            x = Real("%s" % candidate1)
            y = Real("%s" % candidate2)
            op1 = random.choice(real_op)
            op2 = random.choice(real_com)
            if op2 in [operator.lt, operator.gt]:
                return Not(op2(op1(x, y), op1(assignment[candidate1], assignment[candidate2])))
            else:
                return op2(op1(x, y), op1(assignment[candidate1], assignment[candidate2]))

        # Code for handling one integer and one real candidate
        elif sort_idx1 == 0 and sort_idx2 == 1:
            x = Int("%s" % candidate1)
            y = Real("%s" % candidate2)
            op0 = random.choice([ToInt, ToReal])
            if op0 in [ToInt]:
                op1 = random.choice(int_op)
                op2 = random.choice(int_com)
                if op2 in [operator.lt, operator.gt]:
                    return Not(op2(op1(x, op0(y)), op1(assignment[candidate1], op0(assignment[candidate2]))))
                else:
                    return op2(op1(x, op0(y)), op1(assignment[candidate1], op0(assignment[candidate2])))
            else:
                op1 = random.choice(real_op)
                op2 = random.choice(real_com)
                if op2 in [operator.lt, operator.gt]:
                    return Not(op2(op1(op0(x), y), op1(op0(assignment[candidate1]), assignment[candidate2])))
                else:
                    return op2(op1(op0(x), y), op1(op0(assignment[candidate1]), assignment[candidate2]))

        # Code for handling two string candidates
        elif sort_idx1 == 2 and sort_idx2 == 2:
            x = String("%s" % candidate1)
            y = String("%s" % candidate2)
            op1 = random.choice([operator.add, PrefixOf, SuffixOf, Contains])
            if op1 in [operator.add]:
                op2 = random.choice(str_com)
                if op2 in [operator.le]:
                    return op2(op1(x, y), op1(assignment[candidate1], assignment[candidate2]))
                else:
                    return Not(op2(op1(x, y), op1(assignment[candidate1], assignment[candidate2])))
            else:
                return operator.eq(op1(x, y), op1(assignment[candidate1], assignment[candidate2]))

        # Code for handling one integer and one string candidate
        elif sort_idx1 == 0 and sort_idx2 == 2:
            op2 = random.choice(str_com)
            x = Int("%s" % candidate1)
            y = String("%s" % candidate2)
            if op2 in [operator.le]:
                return op2(y.at(x), assignment[candidate2].at(assignment[candidate1]))
            else:
                return Not(op2(y.at(x), assignment[candidate2].at(assignment[candidate1])))

        # Code for handling two bit-vector candidates
        elif sort_idx1 == 3 and sort_idx2 == 3:
            x = BitVec("%s" % candidate1, assignment[candidate1].size())
            y = BitVec("%s" % candidate2, assignment[candidate2].size())
            if assignment[candidate1].size() != assignment[candidate2].size():
                return Not(operator.lt(Concat(x, y), Concat(assignment[candidate1], assignment[candidate2])))
            else:
                op1 = random.choice(bv_op)
                return operator.eq(op1(x, y), op1(assignment[candidate1], assignment[candidate2]))

        # Code for handling two regular expression candidates
        elif sort_idx1 == 4 and sort_idx2 == 4:
            op1 = random.choice(re_op)
            return operator.eq(op1(candidate1, candidate2), op1(assignment[candidate1], assignment[candidate2]))

        # Code for handling one string and one regular expression candidate
        elif sort_idx1 == 2 and sort_idx2 == 4:
            return operator.eq(InRe(candidate1, candidate2), InRe(assignment[candidate1], assignment[candidate2]))

        # Return None if the combination of candidates is not supported
        else:
            return None

    # Main function body
    generated_list = list()
    flag = [None] * 20000
    int_nodes = list()
    real_nodes = list()
    string_nodes = list()
    fp_nodes = list()
    bv_nodes = list()
    re_nodes = list()

    # Classify variables based on their types
    for i in range(len(assignment)):
        var = assignment[i]
        flag[i] = var
        if isinstance(assignment[flag[i]], IntNumRef):
            int_nodes.append(flag[i])
        elif isinstance(assignment[flag[i]], RatNumRef):
            real_nodes.append(flag[i])
        elif isinstance(assignment[flag[i]], SeqRef):
            string_nodes.append(flag[i])
        elif isinstance(assignment[flag[i]], BitVecNumRef):
            bv_nodes.append(flag[i])
        elif isinstance(assignment[flag[i]], FPNumRef):
            fp_nodes.append(flag[i])
        elif isinstance(assignment[i], ReRef):
            re_nodes.append(flag[i])

    # Combine all classified nodes into a single list
    all_nodes = int_nodes + real_nodes + string_nodes + bv_nodes + re_nodes

    # If there are at least two nodes, generate snippets by randomly selecting two nodes
    if len(all_nodes) > 1:
        for _ in range(50):
            candidates = random.sample(all_nodes, 2)
            index1 = check_sort(candidates[0], int_nodes, real_nodes, string_nodes, bv_nodes, re_nodes)
            index2 = check_sort(candidates[1], int_nodes, real_nodes, string_nodes, bv_nodes, re_nodes)
            if index1 < index2:
                new = build_snippet(index1, index2, candidates[0], candidates[1], assignment)
            else:
                new = build_snippet(index2, index1, candidates[1], candidates[0], assignment)
            if new is not None:
                generated_list.append(new)

    # If there is only one node, generate a snippet using the single node
    elif len(all_nodes) == 1:
        candidate = all_nodes[0]
        index = check_sort(candidate, int_nodes, real_nodes, string_nodes, bv_nodes, re_nodes)
        if index == 0:
            x = Int("%s" % candidate)
        elif index == 1:
            x = Real("%s" % candidate)
        elif index == 2:
            x = String("%s" % candidate)
        elif index == 3:
            x = BitVec("%s" % candidate, assignment[candidate].size())
        
        single_op = [int_single, real_single, str_single, bv_single, re_single]
        op = random.choice(single_op[index])
        generated_list.append(operator.eq(op(x), op(assignment[candidate])))

    return generated_list


def get_unsat_cores(node_list):
    """
    Get the unsat core of a list of nodes
    """
    s = Solver()
    s.set(unsat_core=True)
    map = dict()
    for idx, node in enumerate(node_list):
        s.assert_and_track(node.node, "f_%s" % idx)
        map["f_%s" % idx] = node.node
    if s.check() == sat:
        return None, None
    else:
        return s.unsat_core(), map


array_op = [Store, Select]

bv_op = [operator.sub, operator.and_, operator.or_, operator.add, operator.mul, operator.truediv, operator.mod, operator.lshift, operator.rshift]
bv_com = [operator.lt]
bv_single = [operator.inv, operator.sub]

int_op = [operator.add, operator.mul, operator.truediv, operator.mod, operator.sub]
int_com = [operator.lt, operator.gt, operator.ge, operator.le]
int_single = [Abs]

real_op = [operator.add, operator.mul, operator.truediv, operator.sub]
real_com = [operator.lt, operator.gt, operator.ge, operator.le]
real_single = [IsInt]

str_op = [operator.add, "at", SubString, PrefixOf, SuffixOf, Contains, IndexOf, Replace]
str_com = [operator.lt, operator.le]
str_single = [Length]

re_op = [Plus, Union, Intersect, Diff]
re_single = [Star, Complement, Option]

conversion = [ToInt, ToReal, IntToStr, StrToInt, Re, StrToCode, StrFromCode, Length]


operators = [int_op, int_op, str_op, bv_op, re_op]


