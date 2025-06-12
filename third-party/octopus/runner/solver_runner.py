
import subprocess
import os
from termcolor import colored



def solver_runner(solver_path, smt_file, temp_core_folder, timeout, incremental, solver, option = None):
    oracle = "unsat" if "unsat" in smt_file else "sat"
    temp_file_name = smt_file.replace(temp_core_folder, "")
    temp_file_name = temp_file_name.replace(".smt2", "")
    temp_file_name += "_output.txt"
    temp_file_path = temp_core_folder +  temp_file_name
    # print(temp_file_path)
    if solver == "cvc5":
        smt_file = "--strings-exp " + smt_file
    if solver in ["yices", "cvc5", "boolector"] and incremental == "yes":
        if option is not None:
            option += " --incremental "
        else:
            option = " --incremental "
        # if option is not None:
        #     command = "timeout " + str(
        #         timeout) + "s " + solver_path + " --incremental " + option + " " + smt_file + " > " + temp_file_path
        # else:
        #     command = "timeout " + str(timeout) + "s " + solver_path + " --incremental " + smt_file + " > " + temp_file_path

    if solver == "cvc5":
        option += " --check-models "
    elif solver == "z3":
        option += " model_validate=true "
    if option is not None:
        command = "timeout " + str(timeout) + "s " + solver_path + " " + option + " " + smt_file + " > " + temp_file_path
    else:
        command = "timeout " + str(timeout) + "s " + solver_path + " " + smt_file + " > " + temp_file_path
    # print(colored(command, "yellow"))

    p = subprocess.Popen(command, shell=True, stderr=subprocess.PIPE)
    terminal_output = p.stderr.read().decode()

    # Process terminal output first before result parsing
    if terminal_output.find("NULL pointer was dereferenced") != -1:
        return "nullpointer", oracle, command
    if terminal_output.find("assert") != -1 or terminal_output.find("AssertionError") != -1 or terminal_output.find(
            "ASSERTION VIOLATION") != -1:
        return "assertviolation", oracle, command
    if terminal_output.find("segfault") != -1 or terminal_output.find("Segmentation fault") != -1:
        return "segfault", oracle, command
    if terminal_output.find("Fatal failure") != -1:
        return "fatalfailure", oracle, command
    if terminal_output.find("Error") != -1:
        return "error", oracle, command

    solver_output = read_result(temp_file_path, incremental, oracle)
    return solver_output, oracle, command




def read_result(file_path, incremental, oracle):
    try:
        with open(file_path, 'r') as f:
            lines = f.read().splitlines()

    except:
        print(colored("CANT OPEN THE FILE", "red", attrs=["bold"]))
        return "error"


    for line in lines:
        if line.find("Parse Error") != -1:
            os.remove(file_path)
            return "parseerror"

        if line.find("Segmentation fault") != -1:
            os.remove(file_path)
            return "segfault"

        # java.lang.NullPointerException
        if line.find("NullPointerException") != -1:
            os.remove(file_path)
            return "nullpointer"

        if line.find("ASSERTION VIOLATION") != -1:
            os.remove(file_path)
            return "assertviolation"

        # java.lang.AssertionError
        if line.find("AssertionError") != -1:
            os.remove(file_path)
            return "assertviolation"
        
        # invalid model
        if line.find("invalid model") != -1:
            os.remove(file_path)
            return "invalidmodel"

        if line.find("CAUGHT SIGNAL 15") != -1:
            os.remove(file_path)
            return "timeout"


    # Uninteresting problems
    for line in lines:
        if line.find("error") != -1 or line.find("unsupported reserved word") != -1:
            os.remove(file_path)
            return "error"
        if line.find("failure") != -1:
            os.remove(file_path)
            return "error"
    if len(lines) == 0:
        os.remove(file_path)
        return "timeout"


    # Incremental mode

    # In this demo, we only consider non-incremental mode
    """
    if incremental == "yes":
        # If any result is unsat, return unsat
        for line in lines:
            if line.find("unsat") != -1:
                os.remove(file_path)
                return "unsat"

        for line in lines:
            if line.find("unknown") != -1:
                os.remove(file_path)
                return "unknown"

        os.remove(file_path)
        return "sat" """


    if len(lines) > 0:
        if lines[0] == "sat" or lines[0] == "unsat" or lines[0] == "unknown":
            os.remove(file_path)
            return lines[0]
        else:
            return "error"
    else:
        os.remove(file_path)
        return "timeout"