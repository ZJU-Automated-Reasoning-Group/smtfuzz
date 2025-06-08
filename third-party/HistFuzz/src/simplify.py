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


import multiprocessing
import random

# from z3 import *

from src.building_blocks import check_sort_func
from src.parsing.Ast import DeclareFun, Define, DeclareConst, DefineConst, FunDecl, Assert, CheckSat, Push, Pop, Term
from src.parsing.TimeoutDecorator import exit_after
from src.skeleton import has_let, process_seed
from src.solver_run.solver import creat_process_and_get_result
from src.utils.file_operation import get_smt_files_list
import os


def standardize_instance(file_path):
    file_list = get_smt_files_list(file_path)
    for f in file_list:
        print(f)
        # if check_sort_func(f):
        standardize_single_instance(f)


def standardize_single_instance(file):
    # Process the SMT formula and extract the variable information
    script, var = process_seed(file)
    new_script = []
    if script is not None:
        # Read the original SMT formula from the file
        with open(file, "r") as f:
            content = f.readlines()
        # Add any "declare-sort" or "define-sort" lines to the new script
        for line in content:
            if "declare-sort" in line or "define-sort" in line:
                new_script.append(line)
        # Add each command in the processed script to the new script
        for i in script.commands:
            # Only add commands with common types
            if check_ast_type(type(i)):
                new_script.append(str(i))
        # Ensure that the "check-sat" command is present at the end of the script
        if len(new_script) > 1:
            if "(check-sat)" not in new_script[-1] and "(check-sat)" not in new_script[-2]:
                new_script.append("(check-sat)")
        elif len(new_script) == 1 and "(check-sat)" not in new_script[-1]:
            new_script.append("(check-sat)")
        # Write the new script to the file
        with open(file, "w") as f2:
            for l in new_script:
                f2.write(l + "\n")
    else:
        # If the formula could not be processed, remove the file
        os.remove(file)



def check_ast_type(ast_type):
    if ast_type in [Define, DefineConst, DeclareConst, DeclareFun, FunDecl, Assert, Push, Pop, CheckSat]:
        return True
    else:
        return False

