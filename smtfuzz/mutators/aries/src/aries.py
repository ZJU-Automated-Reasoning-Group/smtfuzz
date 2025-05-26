from mutate import Mutate, mimetic_mutation
from utils.file_operations import recursively_get_files, get_all_files_recursively
from solver_runner import run_solver, record_bug
from equality_saturation.helper import RewriteEGG, convert_to_IR, convert_IR_to_str, ALL_RULES
from parsing.Parse import parse_file
from parsing.TimeoutDecorator import exit_after


import traceback
import os
import random
import multiprocessing
import psutil
import shutil
import subprocess
import time
import argparse
from argument_parser.parser import MainArgumentParser

from src.parsing.Ast import CheckSat, Assert

MIMETIC_TIMES = 10

def fuzz(seeds, solver, solver_bin, temp_dir, modulo=2, max_iter=10, core=0, bug_type="common", extra_fuzzer=None):
    @exit_after(300)
    def fuzz_each_file(seed_file, solver, solver_bin, temp_dir, modulo=2, max_iter=10, core=0, bug_type="common"):
        """
        Fuzz a seed file.
        """
        print("Processing seed file: {}".format(seed_file))
        script_dir = "{}/script/core{}/{}/".format(temp_dir, str(core), seed_file.split('/')[-1].replace('.smt2', ''))
        if not os.path.exists(script_dir):
            os.makedirs(script_dir)
        initial_seed_filename = seed_file.split("/")[-1]
        soundness_flag = False
        completeness_flag = False
        performance_flag = False
        logic = None
        if logic is None:
            logic = "(set-logic ALL)"
        orig_file_path = seed_file

        if MIMETIC_TIMES >= 0:
            original_smt2 = os.path.join(script_dir, "original.smt2")

            if not os.path.exists(original_smt2):
                shutil.copy(seed_file, original_smt2)

            for mimetic_iter in range(MIMETIC_TIMES):
                mutation_flag = mimetic_mutation(seed_file, original_smt2)
                if not mutation_flag:
                    seed_file = original_smt2
                    orig_file_path = seed_file
        temp_output = script_dir + "/temp.txt"
        orig_output, _, orig_time, command = run_solver(solver_bin, solver, seed_file, 10, "incremental", temp_output, temp_dir, "None", default=True)
        print("Original output: {}".format(orig_output))
        if orig_output == "timeout":
            pass
        new_script = []
        
        for iter in range(max_iter):
            previous_command = command
            TargetScript, TargetGlobal = parse_file(seed_file)
            if TargetScript is None:
                print("TargetScript is None")
                return
            current_ast = TargetScript.assert_cmd
            if new_script == []:
                for cmd in TargetScript.commands:
                    if isinstance(cmd, CheckSat) or "(exit)" in str(cmd):
                        pass
                    elif isinstance(cmd, Assert):
                        pass
                    else:
                        new_script.append(str(cmd))
            replacee_terms = random.sample(TargetScript.op_occs, 3 if len(TargetScript.op_occs) > 3 else len(TargetScript.op_occs))
            replace_pairs = []
            for term in replacee_terms:
                term_ir = convert_to_IR(term)
                term_str = str(term)
                subterms = term.get_all_subterms()
                sexpr = []
                for subterm in subterms:
                    sexpr.append(str(subterm))
                transformed_irs = RewriteEGG(term_ir, ALL_RULES, sexpr, 1)
                if transformed_irs is None or len(transformed_irs) == 0:
                    continue
                transformed_ir = transformed_irs[0]
                new_term_str = convert_IR_to_str(transformed_ir)
                if new_term_str is not None:
                    replace_pairs.append((term_str, new_term_str))

                applied_rules = ""
                if replace_pairs:
                    current_ast_str = ""
                    for ast_cmd in current_ast:
                        current_ast_str += str(ast_cmd) + "\n"
                    for replace_pair in replace_pairs:
                        current_ast_str = current_ast_str.replace(replace_pair[0], replace_pair[1], 1)
                        applied_rules += "Original term is: {}\nRewritten term is: {}\n".format(replace_pair[0], replace_pair[1])
                else:
                    # do not skip this iteration
                    current_ast_str = ""
                    for ast_cmd in current_ast:
                        current_ast_str += str(ast_cmd) + "\n"

                mutated_formula = "\n".join(new_script) + "\n" + current_ast_str + "\n(check-sat)"
            mutant_path = script_dir + "/{}_mutant_{}.smt2".format(initial_seed_filename, str(iter))
            with open(mutant_path, "w") as f:
                # f.write(str(mutated_formula))
                f.write(logic + "\n" + str(mutated_formula))
            if bug_type == "common":
                mutant_output, _, mutant_time, command = run_solver(solver_bin, solver, mutant_path, 10, "incremental", temp_output, temp_dir, "None", default=False, rules=applied_rules)
            else:
                if bug_type == "all":
                    # default = "options"
                    default = True
                mutant_output, _, mutant_time, command = run_solver(solver_bin, solver, mutant_path, 10, "incremental", temp_output, temp_dir, "None", default, rules=applied_rules)
            # print("Mutant output: {}".format(mutant_output))
            if bug_type == "all":
                if mutant_time / orig_time > 10 or ("sat" in orig_output and mutant_output == "timeout"):
                    if not performance_flag:
                        performance_flag = True
                        record_bug(temp_dir, "performance", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                if orig_time / mutant_time > 10 or (orig_output == "timeout" and "sat" in mutant_output ):
                    if not performance_flag:
                        performance_flag = True
                        record_bug(temp_dir, "performance", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                if ("unknown" not in orig_output and "unknown" in mutant_output) or ("unknown" in orig_output and "unknown" not in mutant_output): 
                    if orig_output not in ["parseerror", "error", "timeout"] and mutant_output not in ["parseerror", "error", "timeout"]:
                        if not completeness_flag:
                            completeness_flag = True
                            record_bug(temp_dir, "completeness", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
            if mutant_output not in [orig_output, "crash", "parseerror", "timeout", "error"]:
                # record_bug(seed_file, mutated_formula, orig_output, mutant_output, orig_time, mutant_time)
                if isinstance(orig_output, list) and isinstance(mutant_output, list):
                    result_len = min(len(orig_output), len(mutant_output))
                    bug_found = False
                    for i in range(result_len):
                        if orig_output[i] != mutant_output[i] and orig_output[i] in ["sat", "unsat"] and mutant_output[i] in ["sat", "unsat"]:
                            bug_found = True
                            break
                    if bug_found and not soundness_flag:
                        soundness_flag = True
                        record_bug(temp_dir, "soundness", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                            
                # record_bug(temp_dir, "soundness", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command)
            seed_file = mutant_path
            orig_file_path = mutant_path

    pro = None
    if not os.path.exists(temp_dir):
        os.makedirs(temp_dir)
    if not os.path.exists("{}/script".format(temp_dir)):
        os.mkdir("{}/script".format(temp_dir))
    if os.path.exists("{}/script/core{}".format(temp_dir, str(core))):
        os.system("rm -r {}/script/core{}".format(temp_dir, str(core)))
    os.mkdir("{}/script/core{}".format(temp_dir, str(core)))
    try:
        for seed in seeds:
            try:
                fuzz_each_file(seed, solver, solver_bin, temp_dir, modulo, max_iter, core, bug_type)
                # raise SystemExit
            # if assertion error, stop fuzzing
            except AssertionError:
                print("AssertionError")
                traceback.print_exc()
                continue

            except Exception as e:
                print("Exception: {}".format(e))
                traceback.print_exc()
                continue
                # raise SystemExit
            except KeyboardInterrupt:
                if pro is not None:
                    pro.terminate()
                    pro.join()
                print("KeyboardInterrupt")
                return
    except KeyboardInterrupt:
        print("KeyboardInterrupt")
        raise SystemExit


def get_logic(smt_file):
    with open(smt_file, "r") as f:
        lines = f.readlines()
    for line in lines:
        if line.startswith("(set-logic"):
            return line.split()[1][:-1]
    return None


def main():
    arguments = MainArgumentParser()
    arguments.parse_arguments(argparse.ArgumentParser())
    parsed_arguments = arguments.get_arguments()
    solver = parsed_arguments["solver"]
    solver_bin = parsed_arguments["solverbin"]
    if solver_bin is None or not os.path.exists(solver_bin):
        print("Solver binary does not exist.")
        raise SystemExit
    if solver is None:
        print("Solver does not exist.")
        raise SystemExit

    seed_dir = parsed_arguments["seeds"]
    if not os.path.exists(seed_dir):
        print("Seed directory does not exist.")
        raise SystemExit
    temp_dir = "./temp"
    bug_type = parsed_arguments["mode"]
    if bug_type not in ["soundness", "all"]:
        print("Invalid mode. Please choose from soundness or all.")
        raise SystemExit
    timeout = int(parsed_arguments["timeout"])
    seed_files = recursively_get_files(seed_dir, '.smt2')
    core_num = int(parsed_arguments["cores"])
    random.shuffle(seed_files)
    # split seed files into core_num parts
    seed_files = [seed_files[i::core_num] for i in range(core_num)]
    # run core_num processes
    processes = []
    for idx in range(core_num):
        print("Fuzzing core {}".format(idx))
        p = multiprocessing.Process(target=fuzz, args=(seed_files[idx], solver, solver_bin, temp_dir, 2, timeout, idx, bug_type))
        processes.append(p)
        p.start()
    for process in processes:
        process.join()
        

if __name__ == "__main__":
    main()
    