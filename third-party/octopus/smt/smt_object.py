from runner.z3_python_api import check_satisfiability, convert_ast_to_expression, get_model
from z3 import *
from termcolor import colored
import copy

class smtObject(object):
    def __init__(self, file_path, path_to_mutant_folder):
        self.path_to_orig_smt_file = file_path
        self.path_to_mutant_folder = path_to_mutant_folder
        self.orig_satisfiability = None
        self.valid = True
        self.orig_ast = None
        self.true_nodes = [None] * 100
        self.false_nodes = [None] * 100
        self.assign_num = 0
        self.all_nodes = list()
        self.dummy_ast = None
        self.true_constructed_nodes = [[] for i in range(1000)]
        self.false_constructed_nodes = [[] for i in range(1000)]
        self.generated_nodes = [None] * 100
        self.total_number_of_assertions = 0
        self.complex_nodes = list()
        self.simple_nodes = list()


        try:
            self.orig_ast = parse_smt2_file(file_path)
            self.dummy_ast = parse_smt2_file(file_path)
            self.total_number_of_assertions = len(self.orig_ast)

        except:
            print(colored("Exception while parsing orig smt file", "red", "on_white"))
            self.valid = False
        self.negated_ast = None
        self.model = None
        #self.model_num = 0



    def get_validity(self):
        return self.valid
    def get_orig_ast(self):
        return self.orig_ast
    def get_negated_ast(self):
        return self.negated_ast
    def get_dummy_ast(self):
        return self.dummy_ast
    def get_orig_satisfiability(self):
        return self.orig_satisfiability
    def append_true_node(self, node):
        self.true_nodes.append(node)
    def append_false_node(self, node):
        self.false_nodes.append(node)
    def append_true_constructed_node(self, node):
        self.true_constructed_nodes.append(node)
    def append_false_constructed_node(self, node):
        self.false_constructed_nodes.append(node)
    def append_to_all_nodes(self, node):
        self.all_nodes.append(node)
    def get_all_nodes(self):
        return self.all_nodes
    def get_true_nodes(self):
        return self.true_nodes
    def get_false_nodes(self):
        return self.false_nodes
    def get_true_constructed_nodes(self):
        return self.true_constructed_nodes
    def get_false_constructed_nodes(self):
        return self.false_constructed_nodes
    def get_total_number_of_assertions(self):
        return self.total_number_of_assertions


    def check_satisfiability_without_convert(self, timeout):
        self.orig_satisfiability = check_satisfiability(self.orig_ast, timeout)

    def get_model(self):
        if self.orig_satisfiability == "sat":
            self.model = get_model(self.orig_ast)
        if self.orig_satisfiability == "unsat":
            self.model = get_model(self.negated_ast)
        return self.model


