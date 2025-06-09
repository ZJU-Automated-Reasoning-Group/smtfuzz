import csv
import sys
import argparse
import shutil
import os
import pathlib
import random
import string
import unicodedata

# Add the parent directory to the path so we can import the Parse module
# from the src directory
current_dir = pathlib.Path(__file__).parent.absolute()
current_parent_dir = current_dir.parent.absolute()
# sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) 
sys.path.append(str(current_parent_dir))

# sys.path.append('..')
from src.parsing.Parse import parse_file, parse_str
from src.parsing.Ast import Const, Script, Term, Var, DeclareFun
from src.parsing.Types import BITVECTOR_TYPE


def parse_csv(file_path):
    with open(file_path, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        return [row for row in reader]


def random_var_name():
    # return 'var'.join(random.choices(string.digits, k=5))
    return "var" + ''.join(random.choices(string.digits, k=5))


class Op(object):
    def __init__(self, return_type, operands):
        self.return_type = return_type
        self.operands = operands

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.return_type}, {self.operands})"

    def __str__(self) -> str:
        return self.__repr__()


def read_config():
    config = {}
    mutational_ops = []
    coversions = {}
    with open(str(current_dir) + "/config/config.txt", "r") as f:
        for line in f.readlines():
            if line.startswith(";"):
                continue
            line = line.strip()
            line = line.strip("(")
            line = line.strip(")")
            if line == "":
                continue
            tokens = line.split(" ")
            if ":" in tokens[-1]:
                tokens.pop()
            if config.get(tokens[0]) is None:
                return_type = tokens[-1]
                if len(tokens) > 2:
                    operands = tokens[1:-1]
                config[tokens[0]] = Op(return_type, operands)
            else:
                if tokens[-1] not in config[tokens[0]].return_type:
                    if type(config[tokens[0]].return_type) == list:
                        config[tokens[0]].return_type.append(tokens[-1])
                    else:
                        config[tokens[0]].return_type = [config[tokens[0]].return_type, tokens[-1]]
                    if len(tokens) > 2:
                        if type(config[tokens[0]].operands[0]) == list:
                            config[tokens[0]].operands.append(tokens[1:-1])
                        else:
                            config[tokens[0]].operands = [config[tokens[0]].operands, tokens[1:-1]]

    with open(str(current_dir) + "/config/ops.txt", "r") as f2:
        for line in f2.readlines():
            if line.startswith(";"):
                continue
            line = line.strip()
            if line == "":
                continue
            if "->" in line:
                tokens = line.split("->")
                mutational_ops.append([tokens[0], tokens[1].split(",")])
            else:
                tokens = line.split(",")
                if ":" in tokens[-1]:
                    tokens[-1] = tokens[-1].split(":")[0]
                mutational_ops.append(tokens)
    with open(str(current_dir) + "/config/coversion.txt", "r") as f3:
        for line in f3.readlines():
            if line.startswith(";"):
                continue
            line = line.strip()
            if line == "":
                continue
            tokens = line.split(" -> ")
            before = tokens[0]
            if coversions.get(before) is None:
                coversions[before] = {}
            temp = tokens[1].split(": ")
            after = temp[0]
            coversions[before][after] = temp[1]
    return config, mutational_ops, coversions


op_map, op_mutator, conversions = read_config()

# print(op_map, "\n")
# print(op_mutator, "\n")
# print(conversions, "\n")

RULES = parse_csv(str(current_parent_dir) + '/res/RewriteRule.csv')


def instantiate_rule(rule):
    smt2_str = ""
    contents = rule.split(";")
    # Loop through the contents of the target format
    for idx, content in enumerate(contents):
        if idx == 0:
            # If it's the first content, add it to the smt2_str with an assert command
            ast = content
            smt2_str += "(assert " + ast + ")"
        else:
            # Otherwise, declare a function with the content and add it to the smt2_str
            declare_cmd = "(declare-fun " + content.split(":")[0] + " () " + content.split(":")[1] + ")"
            smt2_str = declare_cmd + "\n" + smt2_str
    # Parse the smt2_str
    s, g = parse_str(smt2_str)
    return s, g


# check whether a str is a path
def is_path(path):
    return os.path.isfile(path)


class Mutate():
    def __init__(self, file):
        # check if it is a file path
        if os.path.isfile(str(file)):
            self.script, self.globs = parse_file(str(file))
        else:
            self.script, self.globs = parse_str(str(file))

        if self.script is None:
            raise ValueError("script should not be None")
        self.rules = RULES
        self.patterns = []
        self.orig_script = []
        self.terms = []
        self._collect_terms()
        self._extract_pattern()
        self.candidate_rewrites = dict()
        for term in self.terms:
            if term is not None and str(term) not in self.candidate_rewrites.keys():
                rule_ids = self._match_rule(term)
                # print(term)
                # print(rule_ids)
                if len(rule_ids) > 0:
                    self.candidate_rewrites[str(term)] = [term, rule_ids]

    def _extract_pattern(self):
        for rule in self.rules:
            target_str = rule['Target']
            self.patterns.append(target_str)
            if "Const" not in target_str and ";" in target_str:
                # smt2_str = ""
                # contents = target_str.split(";")
                # for idx, content in enumerate(contents):
                #     if idx == 0:
                #         ast = content
                #         smt2_str += "(assert " + ast + ")"
                #     else:
                #         declare_cmd = "(declare-fun " + content.split(":")[0] + " () " + content.split(":")[1] + ")"
                #         smt2_str = declare_cmd + "\n" + smt2_str
                # s, g = parse_str(smt2_str)
                s, g = instantiate_rule(target_str)
                self.orig_script.append(s)
            elif "Const" in target_str:
                # print(target_str)
                contents = target_str.split(":")
                const_str = contents[0]
                const_type = contents[1].replace("_Const", "")
                assert_const = Const(const_str, type=const_type)
                # s, g = parse_str("(assert " + target_str + ")")
                self.orig_script.append(assert_const)
            else:
                # assert_var = Var(name=target_str, type=rule['Type'])
                self.orig_script.append(None)

    def _collect_terms(self):
        for i in self.script.op_occs:
            self.terms.append(i)
        for j in self.script.const_occs:
            self.terms.append(j)
        for k in self.script.free_var_occs:
            self.terms.append(k)

    # def _get_same_subterm(self, term):
    #     assert isinstance(term, Term)
    #     euqal_subterms = []
    #     if term.op is not None:
    #         for idx, subterm in enumerate(term.subterms):
    #             temp_list = [idx]
    #             if len(term.subterms) > 1 and idx < len(term.subterms) - 1:
    #                 for i in range(idx + 1, len(term.subterms)):
    #                     if subterm == term.subterms[i]:
    #                         temp_list.append(i)
    #             if len(temp_list) > 1:
    #                 euqal_subterms.append(temp_list)
    #     return euqal_subterms

    def _get_same_subterm(self, term, path=(), all_subterms=None):
        if all_subterms is None:
            all_subterms = []

        # If term is atomic (has no subterms), add it directly with its path
        if not term.subterms:
            all_subterms.append((term, path))
        else:
            # If term has subterms, recursively process each subterm
            for idx, subterm in enumerate(term.subterms):
                self._get_same_subterm(subterm, path + (idx,), all_subterms)

        # This part of the code only runs at the root call (not recursive calls)
        if path == ():
            equal_subterms_indices = []
            # Compare all subterms in all_subterms list
            for idx, (subterm, subpath) in enumerate(all_subterms):
                temp_list = [subpath]
                for i in range(idx + 1, len(all_subterms)):
                    if subterm == all_subterms[i][0]:  # Compare based on subterm equality
                        temp_list.append(all_subterms[i][1])  # Add path if equal
                if len(temp_list) > 1:
                    equal_subterms_indices.append(temp_list)

            return equal_subterms_indices

    def _extract_subterm_with_path(self, term, path):
        """
        Extract the subterm of the term using the path
        """
        if not path:
            return term

        current_term = term
        # if not isinstance(current_term, Term) or current_term.subterms is None:
        #     return None
        for index in path:
            if not isinstance(current_term, Term) or current_term.subterms is None or index >= len(
                    current_term.subterms):
                return None
            current_term = current_term.subterms[index]

        return current_term

    def _compare_term(self, term1, term2):
        """
        Compare two terms to see if they are the same.
        term1: Term in the mutated script
        term2: Term in the rewrite rule
        """
        try:

            if not isinstance(term2, Term):
                return False

            # If the operation of term2 is not None
            if term2.op is not None:
                # If the operations of term1 and term2 are not the same
                if not isinstance(term1, Term) or term1.op != term2.op:
                    return False

                # If the number of subterms of term1 and term2 are not the same
                if len(term1.subterms) != len(term2.subterms):
                    return False

                # check if term2 contains the same subterms
                equal_subterms = self._get_same_subterm(term2)
                # Now equal_subterms contains lists of paths (tuples of indices) to equal subterms.
                for equal_pairs in equal_subterms:
                    # Retrieve the first subterm using the path for comparison.
                    first_subterm_path = equal_pairs[0]
                    # Navigate to the first subterm in term1 using the path.
                    first_subterm = self._extract_subterm_with_path(term1, first_subterm_path)
                    if first_subterm is None:
                        continue

                    # Compare the first subterm with other subterms found to be equal in term2.
                    for idx_path in equal_pairs:
                        if first_subterm_path != idx_path:  # Ensure we're not comparing the subterm with itself.
                            # Navigate to the current subterm in term1 using idx_path.
                            current_subterm = self._extract_subterm_with_path(term1, idx_path)
                            if current_subterm is None:
                                continue

                            # Perform the comparison between first_subterm and current_subterm.
                            # Since we're comparing subterms across different levels, we use the str() representation as a fallback.
                            if first_subterm != current_subterm or str(first_subterm) != str(current_subterm):
                                return False

                # Iterate over the subterms of term2
                for idx, subterm in enumerate(term2.subterms):
                    # If the operation of the subterm is not None
                    if isinstance(subterm, Term) and subterm.op is not None:
                        # If the subterm of term1 and the subterm are not the same
                        if not isinstance(term1.subterms[idx], Term) or not self._compare_term(term1.subterms[idx],
                                                                                               subterm):
                            return False
                    else:
                        # If the operation of the subterm of term1 is not None
                        if isinstance(term1.subterms[idx], str) and not isinstance(subterm, str):
                            return False
                        if isinstance(term1.subterms[idx], Term) and isinstance(subterm, Term):
                            # If the operation of the subterm of term1 is not the same as the type of the subterm
                            if term1.subterms[idx].is_const != subterm.is_const or judge_type(term1.subterms[idx],
                                                                                              self.globs) != subterm.type:
                                return False
                            # If the subterm of term1 is a constant
                            if term1.subterms[idx].is_const and term1.subterms[
                                idx].name != subterm.name and subterm.name != "c":
                                return False
                            # If the type of the subterm of term1 is not the same as the type of the subterm
                            if not term1.subterms[idx].is_const and judge_type(term1.subterms[idx],
                                                                               self.globs) != subterm.type:
                                return False
                        else:
                            # If one is constant and the other is not
                            if isinstance(subterm, str) or isinstance(term1.subterms[idx], str):
                                return False

                # If all checks pass, the terms are the same
                return True

            # If the operation of term2 is None
            elif term2.op is None:
                # If the operation of term1 is not None
                if term1.op is not None and op_map[term1.op] != term2.type:
                    return False
                # If the type of term1 is not the same as the type of term2
                if term1.op is None and term1.type != term2.type:
                    return False
                # If all checks pass, the terms are the same
                return True
        except Exception as e:
            # print(e)
            return False

    def _match_rule(self, term):
        if term is None:
            raise ValueError("term should not be None")

        rule_ids = []
        if isinstance(term, str):
            pass
        elif isinstance(term, Term):
            # print(term)
            for idx, rule in enumerate(self.orig_script):
                # print(type(term))
                if term.is_const and isinstance(rule, Term):
                    if term.type == rule.type and str(term) == str(rule):
                        rule_ids.append(idx)
                elif not term.is_const and isinstance(rule, Script):
                    assert isinstance(term, Term)
                    eq_symbol = self._compare_term(term, rule.assert_cmd[0].term)
                    if eq_symbol:
                        rule_ids.append(idx)
        return tuple(rule_ids)

    def mutate_term(self, term, rule_id):
        """
        Mutate the term according to the rewrite rule
        """
        # Get the rule from the rules list using the rule_id
        if not isinstance(term, Term):
            return self.script
        rule = self.rules[rule_id]
        # Get the current format of the script
        current_format = self.orig_script[rule_id]
        # Get the target format from the rule
        target_format = rule['Original']
        # smt2_str = ""
        # contents = target_format.split(";")
        # # Loop through the contents of the target format
        # for idx, content in enumerate(contents):
        #     if idx == 0:
        #         # If it's the first content, add it to the smt2_str with an assert command
        #         ast = content
        #         smt2_str += "(assert " + ast + ")"
        #     else:
        #         # Otherwise, declare a function with the content and add it to the smt2_str
        #         declare_cmd = "(declare-fun " + content.split(":")[0] + " () " + content.split(":")[1] + ")"
        #         smt2_str = declare_cmd + "\n" + smt2_str
        # Parse the smt2_str
        s, g = instantiate_rule(target_format)
        replacer_pairs = []
        # If the current format is a Term
        if isinstance(current_format, Term):
            # Loop through the free variables in the parsed string
            for global_var in s.free_var_occs:
                # If the type of the variable is in the global variables
                if global_var.type in self.globs.values():
                    # Loop through the free variables in the script
                    for formula_var in self.script.free_var_occs:
                        # If the types match, add them to the replacer pairs
                        if formula_var.type == global_var.type:
                            replacer_pairs.append([global_var, formula_var])
                else:
                    # Otherwise, create a new variable and add it to the replacer pairs
                    new_var = random_var_name()
                    replacer_pairs.append([global_var, Var(name=new_var, type=global_var.type)])
            # Classify the replacer pairs by the first element
            classified_replacer_pairs = {}
            for pair in replacer_pairs:
                if classified_replacer_pairs.get(str(pair[0])) is None:
                    classified_replacer_pairs[str(pair[0])] = [[pair[0], pair[1]]]
                else:
                    if [pair[0], pair[1]] not in classified_replacer_pairs[str(pair[0])]:
                        classified_replacer_pairs[str(pair[0])].append([pair[0], pair[1]])
            # Get the term from the assert command in the parsed string
            new_term = s.assert_cmd[0].term
            new_declare_cmd = []
            # Loop through the classified replacer pairs
            if not classified_replacer_pairs:
                return self.script
            for key, value in classified_replacer_pairs.items():
                if len(value) > 1:
                    # If there is more than one pair, choose one randomly
                    replace_candidate = random.choice(value)
                else:
                    # Otherwise, use the only pair
                    replace_candidate = value[0]
                # Substitute the old term with the new one in the new term
                new_term.substitute(replace_candidate[0], replace_candidate[1])
                # Add a declare function command for the new variable to the new declare commands
                new_declare_cmd.append(DeclareFun(replace_candidate[1].name, "", replace_candidate[1].type))
            # Loop through the assert commands in the script
            for assert_cmd in self.script.assert_cmd:
                # Substitute the old term with the new one in the term of the assert command
                if not isinstance(assert_cmd.term, Term):
                    continue
                assert_cmd.term.substitute_specific_num(term, new_term, random.randint(1, 3))
                # If the name of the new variable is not in the global variables, add it
                if replace_candidate[1].name not in self.globs.keys():
                    self.globs[replace_candidate[1].name] = replace_candidate[1].type
                    # Add the new declare commands to the commands
                    self.script.commands = new_declare_cmd + self.script.commands
        else:
            # If the current format is not a Term, get the term from the assert command in the current format
            current_script = current_format
            current_format = current_format.assert_cmd[0].term
            # Get the term from the assert command in the parsed string
            new_term = s.assert_cmd[0].term
            if not isinstance(new_term, Term):
                return self.script

            new_term_str = str(new_term)
            if len(current_script.free_var_occs) < len(s.free_var_occs):
                for new_term_var in s.free_var_occs:
                    if new_term_var not in current_script.free_var_occs:
                        for global_var in self.script.free_var_occs:
                            if global_var.type == new_term_var.type:
                                replacer_pairs.append([new_term_var, global_var])
                            else:
                                new_var = random_var_name()
                                replacer_pairs.append([new_term_var, Var(name=new_var, type=new_term_var.type)])
                classified_replacer_pairs = {}
                for pair in replacer_pairs:
                    if classified_replacer_pairs.get(str(pair[0])) is None:
                        classified_replacer_pairs[str(pair[0])] = [[pair[0], pair[1]]]
                    else:
                        if [pair[0], pair[1]] not in classified_replacer_pairs[str(pair[0])]:
                            classified_replacer_pairs[str(pair[0])].append([pair[0], pair[1]])
                new_declare_cmd = []
                for key, value in classified_replacer_pairs.items():
                    if len(value) > 1:
                        replace_candidate = random.choice(value)
                    else:
                        replace_candidate = value[0]
                    new_term.substitute(replace_candidate[0], replace_candidate[1])
                    new_declare_cmd.append(DeclareFun(replace_candidate[1].name, "", replace_candidate[1].type))
                    if replace_candidate[1].name not in self.globs.keys():
                        self.globs[replace_candidate[1].name] = replace_candidate[1].type
                        self.script.commands = new_declare_cmd + self.script.commands
            # Assert that the operator of the current format is not None and the number of subterms match
            # assert current_format.op is not None and len(current_format.subterms) == len(term.subterms)
            if current_format.op is not None and len(current_format.subterms) == len(term.subterms):
                if len(current_format.subterms) == 1 and current_format.subterms[0].op is not None and term.subterms[
                    0].op is not None:
                    if current_format.subterms[0].op is not None and len(current_format.subterms[0].subterms) == len(
                            term.subterms[0].subterms):
                        # Loop through the subterms of the current format
                        for idx, subterm in enumerate(current_format.subterms[0].subterms):
                            # Substitute the old subterm with the new one in the new term
                            new_term.substitute(subterm, term.subterms[0].subterms[idx])
                        # Loop through the assert commands in the script
                        for assert_cmd in self.script.assert_cmd:
                            if not isinstance(assert_cmd.term, Term):
                                continue
                            # Substitute the old term with the new one in the term of the assert command
                            assert_cmd.term.substitute_specific_num(term, new_term, random.randint(1, 3))
                elif len(current_format.subterms) != 1:
                    # Loop through the subterms of the current format
                    for idx, subterm in enumerate(current_format.subterms):
                        # Substitute the old subterm with the new one in the new term
                        new_term.substitute(subterm, term.subterms[idx])
                    # Loop through the assert commands in the script
                    for assert_cmd in self.script.assert_cmd:
                        if not isinstance(assert_cmd.term, Term):
                            continue
                        # Substitute the old term with the new one in the term of the assert command
                        assert_cmd.term.substitute_specific_num(term, new_term, random.randint(1, 3))

            elif current_format.op is None and term.op is None:
                # If the current format and the term are both constants, substitute the current format with the term
                new_term.substitute(current_format, term)
                for assert_cmd in self.script.assert_cmd:
                    if not isinstance(assert_cmd.term, Term):
                        continue
                    assert_cmd.term.substitute_specific_num(term, new_term, random.randint(1, 3))
            if new_term_str in str(self.script):
                # If the new term is already in the script, return the script
                print(new_term_str)
            # assert new_term_str not in str(self.script)
        # Return the script
        return self.script


def convert(term, orig, target):
    def random_op(candidates):
        # Split the candidates if multiple options are available, and choose one randomly
        candidates = candidates.split(", ") if ", " in candidates else [candidates]
        return random.choice(candidates)

    def select_op_seq(orig, target):
        op_seq = []
        # print(conversions.get(orig))
        # Check if conversions for the original type exist
        if conversions.get(orig):
            # Check if a conversion to the target type exists
            op = conversions[orig].get(target)
            if op:
                # Split the operations if multiple operations are required
                ops = op.split("-") if "-" in op else [op]
                # Choose a random operation if multiple options are available
                op_seq = [random_op(op) for op in ops]
        return op_seq

    if orig != target:
        ops = select_op_seq(orig, target)
        if ops:
            for op in ops:
                if op == "int2bv" and isinstance(target, BITVECTOR_TYPE):
                    # term = "((_ int2bv {}) {})".format(str(target.bitwidth), str(term))
                    pass
                elif op != "ite":
                    # term = "({} {})".format(op, str(term))
                    term = Term(op=op, subterms=[term], type=target)
                else:
                    # term = "({} {} {})".format(op, str(term), str(term))
                    # term = Term(op="ite", subterms=[term, term, term], type=target)
                    pass
            return term
        else:
            return False


def is_number(s):
    """Check if the input string s is a number."""
    try:
        # Try to convert the string to float
        float(s)
        return True
    except ValueError:
        # If a ValueError occurs, it means the string is not a float number
        pass

    try:
        # Try to convert a string representing a number to a float

        unicodedata.numeric(s)
        return True
    except (TypeError, ValueError):
        # If a TypeError or ValueError occurs, it means the string is not a number
        pass

    # If all the above checks fail, the string is not a number
    return False


def judge_type(term, glob_vars):
    def get_type(term):
        if isinstance(term, Term):
            if term.op:
                op_map_value = op_map.get(term.op)
                if op_map_value is not None:
                    if isinstance(op_map_value.return_type, list) and len(op_map_value.return_type) > 1:
                        return "Unknown"
                    else:
                        type_map = {"Int": "Int", "Real": "Real", "Bool": "Bool", "String": "String", "RegEx": "RegEx"}
                        return type_map.get(
                            op_map_value.return_type) if op_map_value.return_type in type_map.keys() else "Unknown"
                else:
                    return "Unknown"

            elif term.is_var:
                return term.type
            elif term.is_const:
                if str(term).isdigit():
                    return "Int"
                elif is_number(str(term)):
                    return "Real"
                elif str(term) in ["true", "false"]:
                    return "Bool"
                else:
                    return "String"
            else:
                return "Unknown"
        else:
            return "Unknown"

    # if op is not None:
    if isinstance(term, Term) and term.op is not None:
        op = term.op
        op_map_value = op_map.get(op)
        # print(op_map_value)
        if op_map_value is not None:
            if isinstance(op_map_value.return_type, list) and len(op_map_value.return_type) > 1:
                # for var, var_type in glob_vars.items():
                #     if str(var) in str(term):
                #         return var_type
                check_list = []
                if term.subterms:
                    check_list += term.subterms
                    for subterm in check_list:
                        subterm_type = get_type(subterm)
                        if subterm_type in ["Int", "Real"]:
                            return subterm_type
                        else:
                            if subterm.subterms:
                                check_list += subterm.subterms
                                # if judge_type(term.subterms[0], glob_vars) == "Int":
                #     return "Int"
                # elif judge_type(term.subterms[0], glob_vars) == "Real":
                #     return "Real"
                return "Unknown"
            else:
                type_map = {"Int": "Int", "Real": "Real", "Bool": "Bool", "String": "String", "RegEx": "RegEx"}
                return type_map.get(
                    op_map_value.return_type) if op_map_value.return_type in type_map.keys() else "Unknown"
    else:
        if term.is_var:
            return term.type
        elif term.is_const:
            if str(term).isdigit():
                return "Int"
            elif is_number(str(term)):
                return "Real"
            elif str(term) in ["true", "false"]:
                return "Bool"
            else:
                return "String"
        else:
            return "Unknown"


def mimetic_mutation(smt_file, new_path):
    """
    Perform mimetic mutation on an SMT file.
    """
    try:
        script, globs = parse_file(smt_file)
        terms = get_terms_from_script(script)
        mimetic_pattern = get_random_pattern()
        # mimetic_pattern = ":String_Const"
        if len(terms) == 0:
            return False
        orig_term = get_random_term(terms)
        # print(mimetic_pattern)
        # print(orig_term)
        modified_term = perform_mutation(orig_term, mimetic_pattern, script, globs)
        if script:
            new_script_str = str(script)
            if new_script_str == "":
                return False
            with open(new_path, "w") as f:
                f.write(new_script_str)
            return modified_term

        return False
    except Exception as e:
        return False


def get_terms_from_script(script):
    return script.op_occs + script.free_var_occs


def get_random_pattern():
    patterns = [rule['Target'] for rule in RULES]
    return random.choice(patterns)


def get_random_term(terms):
    random_term = random.choice(terms)
    # while str(random_term) != "NEW_DGNode_769":
    #     random_term = random.choice(terms)
    return random_term


def perform_mutation(orig_term, mimetic_pattern, script, globs):
    orig_term_sort = judge_type(orig_term, globs)
    if "_Const" not in mimetic_pattern and ";" in mimetic_pattern:
        mimetic_script, mimetic_vars = instantiate_rule(mimetic_pattern)
        mimetic_term = mimetic_script.assert_cmd[0].term
        if isinstance(mimetic_term, str):
            mimetic_term = Const(mimetic_term)
        if mimetic_vars:
            mutation_flag = perform_variable_mutation(orig_term, mimetic_vars, mimetic_term, globs)
            if not mutation_flag:
                return None
        elif mimetic_term.is_var:
            new_term = convert(orig_term, orig_term_sort, mimetic_term.type)
            if not new_term:
                return None
            mimetic_term = new_term
        elif mimetic_term.is_const:
            pass
    else:
        if mimetic_pattern.startswith(":"):
            mimetic_term = Const("\"\"", type="String")
        else:
            mimetic_term = Const(mimetic_pattern.split(":")[0],
                                 type=mimetic_pattern.split(":")[1].replace("_Const", ""))

    mimetic_term_sort = judge_type(mimetic_term, globs)
    if mimetic_term_sort != "Unknown" and orig_term_sort != "Unknown" and mimetic_term_sort != orig_term_sort:
        mimetic_term = convert(mimetic_term, mimetic_term_sort, orig_term_sort)
        if not mimetic_term:
            return None
    if mimetic_term != orig_term:
        for assert_cmd in script.assert_cmd:
            assert_cmd.term.substitute_specific_num(orig_term, mimetic_term, random.randint(1, 3))
    return mimetic_term


def perform_variable_mutation(orig_term, mimetic_vars, mimetic_term, globs):
    for var in mimetic_vars.keys():
        replacee = Var(name=var, type=mimetic_vars[var])
        replacee_sort = mimetic_vars[var]
        rand_subterm = get_random_subterm(orig_term)
        rand_subterm_sort = judge_type(rand_subterm, globs)
        if replacee_sort != "Unknown" and rand_subterm_sort != "Unknown" and replacee_sort != rand_subterm_sort:
            new_term = convert(rand_subterm, rand_subterm_sort, replacee_sort)
            if not new_term:
                return False
        else:
            new_term = rand_subterm
        if new_term != replacee:
            mimetic_term.substitute(replacee, new_term)


def get_random_subterm(orig_term):
    if orig_term.subterms:
        return random.choice(orig_term.subterms)
    else:
        return orig_term
