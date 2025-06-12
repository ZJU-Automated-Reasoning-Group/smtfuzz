
from termcolor import colored
from z3 import *
from utils.file_operations import create_smt2_file
import copy



def export_mutants(mutants, oracles, path):
    """
        :param asts: List of ast objects
        :param path: export path
        :return:
    """
    # dummy_ast = smt_object.get_dummy_ast()
    file_num = 0
    for k ,ast_set in enumerate(mutants):
        for i, ast in enumerate(ast_set):
            # new_ast = copy.deepcopy(dummy_ast)
            # new_ast.resize(0)
            s = Solver()
            for j, assertion in enumerate(ast):
                # new_ast.push(assertion)
                s.add(assertion)
            smt2_string = s.to_smt2()
            print_success_false_string = "(set-option :print-success false)\n"
            theory_string = "(set-logic ALL)\n"
            smt2_string = print_success_false_string + theory_string + smt2_string
            file_path = os.path.join(path, oracles[k][i] + "_" + str(file_num) + ".smt2")
            create_smt2_file(file_path, smt2_string)
            file_num = file_num + 1


def enrich_true_and_false_nodes(smt_object, snippets, enrichment_steps, randomness, max_depth):
    """
        Populate true_constructed_nodes and false_constructed_nodes with more complex trees.
        These trees are created by AND-ing or NOT-ing random nodes in true_nodes and false_nodes
        Obviously this is for the case when the original formula is SAT and we have a model
    """
    constructed_formulas = []
    for j, snippet in enumerate(snippets):
        enrichment_set = list()
        candidates = smt_object + snippet
        # prior_true_choice = 0
        # prior_false_choice = 0
        for i in range(enrichment_steps):
            # Choose an operator
            f1 = randomness.random_choice(candidates)
            f2 = randomness.random_choice(candidates)
            if isinstance(f1, AstRef):
                v1 = True
            else:
                v1 = f1.truth_values[j]
                f1 = f1.node
            if isinstance(f2, AstRef):
                v2 = True
            else:
                v2 = f2.truth_values[j]
                f2 = f2.node
                
            if v1 and v2:
                op = randomness.random_choice([And, Or, Implies])
            elif v1 and not v2:
                op = randomness.random_choice([Or, Xor])
            elif not v1 and v2:
                op = randomness.random_choice([Or, Implies, Xor])
            elif not v1 and not v2:
                op = randomness.random_choice([Implies])
            enrichment_set.append(op(f1, f2))
            candidates.append(op(f1, f2))
                # if node_1_depth <= max_depth and node_2_depth <= max_depth:
        constructed_formulas.append(enrichment_set)
    return constructed_formulas

def pick_true_and_false_nodes_at_random(formulas, number_of_mutants, max_assertions, randomness, unsat_core=None, maps=None, target=None):
    """
        Depending on the size of the true_nodes and false_nodes
        Generate new ASTs
        Appends generation vector
    """
    group_count = len(formulas)
    mutants = [[] for u in range(group_count)]    # A list of a list of assertions
    oracles = [[] for v in range(group_count)]
    if unsat_core is not None and target is None:
        target = ["sat", "unsat", "sat"]
        # target = ["unsat"]
    elif unsat_core is not None and target == "unsat":
        target = ["unsat"]
    else:
        target = ["sat"]
    for i in range(number_of_mutants):
        number = i % group_count
        oracle = randomness.random_choice(target)
        oracles[number].append(oracle)
        if oracle == "sat":
            mutant_file = list()    # A list of assertions
            number_of_assertions = randomness.get_a_non_prime_integer(max_assertions)
            for i in range(number_of_assertions):
                # Make a decision about picking either a simple node or an enriched node
                # node_decision = randomness.random_choice(["simp", "simp","enr","enr","enr","enr","enr","enr","enr","enr"])
                    # pick a true of false constructed node
                node_choice = randomness.random_choice(formulas[number])
                node = node_choice
                    #smt_object.false_constructed_nodes[number].remove(node_choice)
                mutant_file.append(node)
        elif oracle == "unsat":
            mutant_file = list()
            number_of_assertions = randomness.get_a_non_prime_integer(max_assertions)
            for idx, label in enumerate(unsat_core):
                if idx == 0:
                    unsat_formula = maps[str(label)]
                else:
                    unsat_formula = And(unsat_formula, maps[str(label)])

            for i in range(number_of_assertions):
                node_choice = randomness.random_choice(formulas[number])
                node = node_choice
                mutant_file.append(node)
            mutant_file.append(unsat_formula)
        mutants[number].append(mutant_file)
    return mutants, oracles

def get_tree_depth(assertion, maxDepth, optimization=True):
    def get_tree_depth_iterative(tree):
        # Iterative algorithm to find the height of a tree
        if not is_and(tree) and not is_or(tree):
            return 0
        q = []
        q.append(tree)
        height = 0
        while (True):
            nodeCount = len(q)
            if nodeCount == 0:
                return height
            height += 1
            # Optimization
            # If the height has already exceeded the maxDepth, no need go any deeper
            if optimization and height > maxDepth:
                return maxDepth + 1
            while nodeCount > 0:
                node = q[0]
                q.pop(0)
                children = node.children()
                left_child = children[0]
                right_child = children[1]
                if is_and(left_child) or is_or(left_child):
                    q.append(left_child)
                if is_and(right_child) or is_or(right_child):
                    q.append(right_child)
                nodeCount -= 1
    try:
        depth = get_tree_depth_iterative(tree=assertion)
    except Exception as e:
        print(colored("Exception while computing tree depth" + str(e)))
        return 1000000
    return depth


def add_check_sat_using(exported_mutant_file_path, check_sat_using_option):
    """
        Replace the normal (check-sat) with (check-sat-using)
    """
    try:
        with open(exported_mutant_file_path, 'r') as f:
            lines = f.read().splitlines()
    except:
        print("#######" +  colored("ERROR OCCURRED IN 'check_sat_using'", "red", attrs=["bold"]))
    for i in range(len(lines)):
        if lines[i].find("(check-sat)") != -1:
            lines[i] = "(check-sat-using " + check_sat_using_option + ")" + "\n"
        else:
            lines[i] = lines[i] + "\n"
    file = open(exported_mutant_file_path, "w")
    file.writelines(lines)
    file.close()


"""
    Helper functions for generation of incremental instances
"""

def count_assertions(file_path):
    with open(file_path, 'r') as f:
        lines = f.read().splitlines()
    no_assertions = 0
    for line in lines:
        if line.find("(assert") != -1:
            no_assertions += 1

    return no_assertions

def get_factor(n, randomness):
    """
        returns a random factor for n and total number of factors
    """
    factors = list()
    for i in range(1, n):
        if n % i == 0:
            factors.append(i)
    return randomness.random_choice(factors), len(factors)


def insert_pushes_pops(mutant_file_paths, randomness):
    """
        Insert pushes and pops in the already exported files
    """
    print("####### Inserting pushes and pops")
    for file_path in mutant_file_paths:
        number_of_assertions = count_assertions(file_path)
        random_factor, number_of_factors = get_factor(number_of_assertions, randomness)
        interval = int(number_of_assertions / random_factor)
        lines = []
        with open(file_path, 'r') as f:
            lines = f.read().splitlines()
        counter = interval
        header_text = True
        push_number = 0
        for i in range(len(lines)):
            if lines[i].find("(assert") != -1:
                header_text = False
                if counter == interval:
                    lines[i] = "\n(push " + str(interval) + ")" + "\n  (assert\n"
                    counter = 1
                    push_number += 1
                else:
                    counter += 1
                    lines[i] = "  " + lines[i] + "\n"
            else:
                if header_text or lines[i].find("check-sat") != -1:
                    lines[i] = lines[i] + "\n"
                else:
                    lines[i] = "  " + lines[i] + "\n"
            if lines[i].find("(push") != -1 and push_number > 1:
                lines[i] = "(pop " + str(randomness.get_random_integer(0, interval)) + ")\n" + lines[i]
                lines[i] = "(check-sat)\n" + lines[i]
        file = open(file_path, "w")
        file.writelines(lines)
        file.close()

    print("####### Insertion of pushes and pops successful")
