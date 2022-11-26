# coding: utf-8
"""
A simple tool for mutating SMT formulas (based on Z3's Python API)
"""
from typing import List
import argparse
import random
import z3
from z3.z3util import get_vars
import os

g_prune_file = False
g_file_name = ""


def get_preds(expr: z3.ExprRef) -> List[z3.ExprRef]:
    """Get atomic predicates of expr"""
    s = set()

    def get_preds_(exp):
        if exp in s:
            return
        if z3.is_not(exp):
            s.add(exp)
        if z3.is_and(exp) or z3.is_or(exp):
            for e_ in exp.children():
                get_preds_(e_)
            return
        assert (z3.is_bool(exp))
        s.add(exp)

    # convert to NNF and then look for preds
    ep = z3.Tactic('nnf')(expr).as_expr()
    get_preds_(ep)
    return list(s)


def string2file(fn: str, string: str) -> None:
    """Write to file"""
    with open(fn, "w") as f:
        f.write(string)


def get_script_from_file(file: str) -> str:
    """Read file"""
    with open(file, "r") as reader:
        script = reader.read()
    return script


def shift_script(script: str) -> str:
    """Filter something in the script
      E.g., som solvers do not handle specific commands
    """
    script_text = script.split('\n')
    new_script_text = ""
    for line in script_text:
        if not ("set-option" in line or "set-info" in line):
            new_script_text = new_script_text + "\n" + line
    return new_script_text


class CubeMutation:
    def __init__(self):
        self.logic = None
        self.success = False
        self.formula = None
        self.assertions = []  # all asserts (one aseert can be complex)
        self.vars = []  # all vars
        self.preds = []  # all atoms

    def init_from_file(self, seed: str):
        try:
            script = get_script_from_file(seed)
            new_script = shift_script(script)
            self.assertions = z3.parse_smt2_string(new_script)
            len_ass = len(self.assertions)
            if len_ass < 1:
                return
            elif len_ass == 1:
                self.formula = self.assertions[0]
            else:
                self.formula = z3.And(self.assertions)
            self.vars = get_vars(self.formula)
            for p in get_preds(self.formula):
                if not (z3.is_true(p) or z3.is_false(p)):
                    self.preds.append(p)
            self.success = True
        except Exception as ex:
            print("error while parsing orig smt file")
            print(ex)

    def get_cube_mutant_as_str(self):
        if len(self.preds) <= 1:
            if g_prune_file:
                os.remove(g_file_name)
                exit(0)
        sol = z3.Solver()
        sol.add(self.formula)
        preds_names = []
        i = 0
        # self.preds is the set of atomic predicates (obtained after NNF transformation)
        for pred in self.preds:
            bi = z3.Bool("l" + str(i))
            preds_names.append("l" + str(i))
            sol.add(bi == pred)
            i = i + 1
        smt2_string = sol.to_smt2()
        # TODO: 1. sample 50%, 75%, 100% of the full set?
        #      2. Consider also the negation of an atom
        for _ in range(10):
            cube = ""
            sample_preds = random.sample(preds_names, 2)
            for p in sample_preds:
                cube += p
                cube += " "
            smt2_string += "(check-sat-assuming ({}))\n".format(cube)
        return smt2_string

    # npred = len(preds_names)
    # sample_preds = random.sample(preds_names, random.randint(1, npred))

    def get_mutant_as_str(self):
        smt2_string = self.get_cube_mutant_as_str()
        return smt2_string


def main(problem_file: str, output_file: str):
    """
    Perform cube-based mutations
    @param problem_file: the seed formula
    @param output_file: the file for writing the mutant
    @return: None
    """
    z3_gene = CubeMutation()
    z3_gene.init_from_file(problem_file)
    # Generate the mutant to the file
    try:
        final_fml_str = ""
        if z3_gene.success:
            smt2_string = z3_gene.get_cube_mutant_as_str()
        else:
            print("fatal failure in mutating!")
            if g_prune_file:
                os.remove(g_file_name)
                exit(0)
            return
        final_fml_str += smt2_string
        # finally, write to file
        string2file(output_file, final_fml_str)
    except Exception as ex:
        print("fatal failure in mutating!")
        print(ex)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', dest='input', default='default', type=str)
    parser.add_argument('--output', dest='output', default='default', type=str)
    args = parser.parse_args()
    g_file_name = args.input
    main(args.input, args.output)
