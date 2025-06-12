import argparse
import multiprocessing
import random
import time
from termcolor import colored
from fuzzer.fuzzer import generate_mutants
from parsing.Parse import parse_file
from fuzzer.helper_functions import add_check_sat_using, insert_pushes_pops
from runner.solver_runner import solver_runner
from smt.smt_object import smtObject
from utils.file_operations import get_all_smt_files_recursively, create_server_core_directory, \
    refresh_directory, \
    get_mutant_paths, pick_a_supported_theory, record_soundness, record_crash
from parsers.argument_parser import MainArgumentParser
from utils.max_depth import get_max_depth, count_asserts, count_lines
from utils.randomness import Randomness
#from config import config
from z3 import *
from parameters import get_parameters_dict, tactic_choice
import shutil
from utils.file_operations import append_row
from utils.options import z3_options, cvc5_options, bitwuzla_options
import random

ALL_FUZZING_PARAMETERS = None
config = {"home":""}

def run_octopus(start_time, seed_file_paths, parsedArguments, core, SEED, wait, generation_flag, model_number):
    def run_mutants_in_a_thread(path_to_temp_core_directory, signal, seed_file_number, seed_file_path, incrementality,
                                solver, fuzzing_parameters, random_obj):
        mutant_file_paths = get_mutant_paths(path_to_temp_core_directory)
        mutant_file_paths.sort()

        if len(mutant_file_paths) > 0:
            if signal == 1:
                print(colored("\tExperienced timeout while exporting mutants. But we still were able to export some",
                              "magenta", attrs=["bold"]))
            print("####### RUNNING MUTANTS")
            soundness_flag = False
            crash_flag = False
            if solver == "z3":
                # random.sample(z3_options, 2)
                if random.choice(["yes", "no"]) == "yes":
                    opt = " ".join(random.sample(z3_options, 2))
                else:
                    opt = " "
            elif solver == "cvc5":
                if random.choice(["yes", "no"]) == "yes":
                    opt = random.choice(cvc5_options)
                else:
                    opt = " "
            elif solver == "bitwuzla":
                if random.choice(["yes", "no"]) == "yes":
                    opt = random.choice(bitwuzla_options)
            else:
                opt = ""
            for i, mutant_path in enumerate(mutant_file_paths):
                output, oracle, cmd = solver_runner(solver_path=parsedArguments["solverbin"],
                                       smt_file=mutant_path,
                                       temp_core_folder=path_to_temp_core_directory,
                                       timeout=ALL_FUZZING_PARAMETERS["solver_timeout"],
                                       incremental=incrementality,
                                       solver=solver, option=opt)
                print("[" + parsedArguments["solver"] + "]\t" + "[core: " + str(core) + "]\t", end="")
                print("[seed_file: " + str(seed_file_number) + "]\t\t" + "[" + str(i + 1) + "/" + str(
                    len(mutant_file_paths)) + "]\t\t", end="")
                #print("[" + parsedArguments["theory"] + "]\t", end="")

                if output == oracle:
                    print(colored(output, "green", attrs=["bold"]))
                elif (output != oracle and output in ["sat", "unsat"]) or output == "invalidmodel":
                    print(colored(output, "red", attrs=["bold"]))
                    print(mutant_path)
                    print(colored("SOUNDNESS BUG", "white", "on_red", attrs=["bold"]))
                    print("SEED = " + str(SEED))
                    # Handle unsoundness
                    if not soundness_flag:
                        record_soundness(home_directory=config["home"],
                                        seed_file_path=seed_file_path,
                                        buggy_mutant_path=mutant_path,
                                        seed=SEED,
                                        mutant_number=i,
                                        seed_theory=parsedArguments["theory"],
                                        fuzzing_parameters=fuzzing_parameters,
                                        cmd=cmd)
                        soundness_flag = True
                    else:
                        pass
                    # print(colored("Time to bug: ", "magenta", attrs=["bold"]) + str(time.time() - start_time))
                    # print(colored("Iterations to bug: ", "magenta", attrs=["bold"]) + str(i+1))
                elif output == "error":
                    print(colored(output, "white", "on_red", attrs=["bold"]))

                elif output in ["segfault", "assertviolation", "nullpointer", "fatalfailure"]:
                    print(colored(output, "white", "on_red", attrs=["bold"]))
                    print(mutant_path)
                    print(colored("CRASH", "white", "on_red", attrs=["bold"]))
                    print("SEED = " + str(SEED))
                    if not crash_flag:
                        crash_flag = True
                        record_crash(home_directory=config["home"],
                                    seed_file_path=seed_file_path,
                                    buggy_mutant_path=mutant_path,
                                    seed=SEED,
                                    mutant_number=i,
                                    seed_theory=parsedArguments["theory"],
                                    fuzzing_parameters=fuzzing_parameters,
                                    cmd=cmd)
                        
                    else:
                        pass

                else:
                    print(colored(output, "yellow", attrs=["bold"]))
                os.remove(mutant_path)  # remove mutant when processed

    """
        Initalizations
    """
    time.sleep(wait)
    print("Running octopus on a core")
    temp_directory = os.path.join(config["home"], "temp")
    path_to_temp_core_directory = os.path.join(temp_directory, parsedArguments["server"], "core_" + core)
    create_server_core_directory(temp_directory, parsedArguments["server"], core)
    # seed_file_paths = []

    global ALL_FUZZING_PARAMETERS
    # normal mode
    ALL_FUZZING_PARAMETERS = get_parameters_dict(replication_mode=False)


    randomness = Randomness(SEED)
    # randomness.shuffle_list(seed_file_paths)
    # run the file and see if it is SAT or UNSAT
    index  = 0
    # while True:
    for i, file in enumerate(seed_file_paths):
        print("####### [" + str(i) + "] seed: " + file, end="")
        # Refresh core directory
        # file = random.choice(seed_file_paths)
        # seed_file_paths.remove(file)
        refresh_directory(path_to_temp_core_directory)
        incrementality = randomness.random_choice(ALL_FUZZING_PARAMETERS["incremental"])

        script, _ = parse_file(file)
        print("####### [" + str(index) + "] seed: " + file, end="")


        max_depth = ALL_FUZZING_PARAMETERS["max_depth"]
        max_assert = ALL_FUZZING_PARAMETERS["max_assert"]

        # Generate all mutants at once for this file in a thread with a timeout
        signal = generate_mutants(smt_Object=script,
                                  path_to_directory=path_to_temp_core_directory,
                                  maxDepth=max_depth,
                                  maxAssert=max_assert,
                                  seed=SEED,
                                  theory=parsedArguments["theory"],
                                  fuzzing_parameters=ALL_FUZZING_PARAMETERS)

        mutant_file_paths = get_mutant_paths(path_to_temp_core_directory)

        if len(mutant_file_paths) == 0:
            print(colored("NO MUTANTS GENERATED", "red", attrs=["bold"]))
            continue

        # Incremental setting apply to all mutants of a file
        print(
            "####### Setting incrementality with prob: " + colored(str(ALL_FUZZING_PARAMETERS["incremental"]), "yellow",
                                                                   attrs=["bold"]))
        print("####### Incrementality: ", end="")
        if incrementality == "yes":
            # In the demo, we only use non-incremental mode
            print(colored("YES", "green", attrs=["bold"]))
            # mutant_file_paths.sort()
            # insert_pushes_pops(mutant_file_paths, randomness)
        else:
            print(colored("NO", "red", attrs=["bold"]))

        print("####### Adding check-sat-using options with prob: " + colored(
            str(ALL_FUZZING_PARAMETERS["check_sat_using"]), "yellow", attrs=["bold"]))
        for mutant_file_path in mutant_file_paths:
            if randomness.random_choice(ALL_FUZZING_PARAMETERS["check_sat_using"]) == "yes" and parsedArguments[
                "solver"] == "z3":
                # random select Z3's tactic
                tactic_num = randomness.get_random_integer(1, 5)
                if tactic_num > 1:
                    check_sat_using_option = "(then "
                    for j in range(tactic_num):
                        one_tactic = randomness.random_choice(tactic_choice())
                        check_sat_using_option = check_sat_using_option + " " + one_tactic
                    check_sat_using_option = check_sat_using_option + ")"
                else:
                    check_sat_using_option = randomness.random_choice(tactic_choice())
                add_check_sat_using(mutant_file_path, check_sat_using_option)

        # Spawn a new process and run mutants
        process = multiprocessing.Process(target=run_mutants_in_a_thread, args=(path_to_temp_core_directory,
                                                                                signal,
                                                                                index,
                                                                                file,
                                                                                incrementality,
                                                                                parsedArguments["solver"],
                                                                                ALL_FUZZING_PARAMETERS,
                                                                                randomness))
        process.start()
        process.join(ALL_FUZZING_PARAMETERS["mutant_running_timeout"])
        if process.is_alive():
            process.terminate()
            print(colored("TIMEOUT WHILE RUNNING THE MUTANTS", "red", attrs=["bold"]))
            time.sleep(ALL_FUZZING_PARAMETERS[
                           "solver_timeout"])  # Wait for the solver to finish processing the last file before deleting the temp dir
        refresh_directory(path_to_temp_core_directory)


def main():
    # os.system("clear")
    initial_time = time.time()
    print(colored("##########################", "blue", "on_white", attrs=["bold"]))
    print(colored("       octopus v.1.0      ", "blue", "on_white", attrs=["bold"]))
    print(colored("##########################", "blue", "on_white", attrs=["bold"]))
    arguments = MainArgumentParser()
    arguments.parse_arguments(argparse.ArgumentParser())
    parsedArguments = arguments.get_arguments()
    print(parsedArguments)

    SEED = parsedArguments["seed"]

    if parsedArguments["benchmark"] is None:
        print(colored("--benchmark argument cannot be None", "red", attrs=["bold"]))
        return 1
    if parsedArguments["solver"] is None:
        print(colored("--solver argument cannot be None", "red", attrs=["bold"]))
        return 1
    if parsedArguments["solverbin"] is None:
        print(colored("--solverbin argument cannot be None", "red", attrs=["bold"]))
        return 1


    try:
        # path_to_theory = os.path.join(parsedArguments["benchmark"], parsedArguments["theory"])
        seed_file_paths_list = get_all_smt_files_recursively(parsedArguments["benchmark"])
        generation_flag = parsedArguments["generation"]
        model_number = int(parsedArguments["assignments"])
        if parsedArguments["cores"] is not None:
            for i in range(int(parsedArguments["cores"])):
                core = i + int(parsedArguments["core"])
                wait = int(parsedArguments["cores"])
                process = multiprocessing.Process(target=run_octopus, args=(
                    initial_time, seed_file_paths_list, parsedArguments, str(core), SEED, wait, generation_flag, model_number))
                process.start()
                # pin the process to a specific CPU
                # os.system("taskset -p -c " + str(i) + " " + str(process.pid))
        else:
            run_octopus(initial_time, seed_file_paths_list, parsedArguments, parsedArguments["core"], SEED, 0, generation_flag, model_number)

    except (KeyboardInterrupt, SystemExit):
        print("\nGood Bye!\n")


if __name__ == '__main__':
    main()


# 492 15