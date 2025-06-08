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

import random
import os
import shutil
import subprocess
import multiprocessing
import time

z3_folder = "/home/coverage/z3-cov"
cvc5_folder = "/home/coverage/cvc5-cov/build"
z3_bin = "/home/coverage/z3-cov/build/z3"
cvc5_bin = "/home/coverage/cvc5-cov/build/bin/cvc5"


"""
def random_sample(files, dst_path):
    selected_files = random.sample(files, 10000)
    for i, file in enumerate(selected_files):
        print(i)
        shutil.copy2(file, dst_path)
"""

def get_all_smt_files_recursively(path_to_directory):
    file_paths = list()
    for r, d, f in os.walk(path_to_directory):
        for file in f:
            if ".smt20" in file:
                continue
            if ".smt2" in file:
                file_path = os.path.join(r, file)
                file_paths.append(file_path)
    return file_paths


def classify_seeds(file_list, solver_bin, file_count=100):
    # op_set = set()
    # result = []
    #print(smt_file)
    file_num = 0
    current_files = []
    if os.path.exists("/home/histfuzz/seeds/LIA/sat") and os.path.exists("/home/histfuzz/seeds/LIA/unsat"):
        return
    if not os.path.exists("/home/histfuzz/seeds/LIA/sat"):
        os.makedirs("/home/histfuzz/seeds/LIA/sat")
    if not os.path.exists("/home/histfuzz/seeds/LIA/unsat"):
        os.makedirs("/home/histfuzz/seeds/LIA/unsat")
    while file_num < file_count:
        smt_file = random.choice(file_list)
        if smt_file in current_files:
            continue
        res = run_solver(solver_bin, smt_file)
        if res == "sat":
            shutil.copy2(smt_file, "/home/histfuzz/seeds/LIA/sat")
            current_files.append(smt_file)
            file_num += 1
        elif res == "unsat":
            shutil.copy2(smt_file, "/home/histfuzz/seeds/LIA/unsat")
            current_files.append(smt_file)
            file_num += 1


def run_solver(solver_bin, smt_file):
    command = "timeout 10s " + solver_bin + " " + smt_file
    p = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    terminal_output = p.stdout.read().decode()
    res = terminal_output.replace("\n", "")
    return res


def run_seeds_coverage(z3_folder, cvc5_folder):
    z3_clear_data = "lcov -d ./ -z"
    cvc_clear_data = "make coverage-reset"
    p1 = subprocess.Popen(z3_clear_data, shell=True, cwd=z3_folder, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
    p2 = subprocess.Popen(cvc_clear_data, shell=True, cwd=cvc5_folder, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
    p1.wait()
    p2.wait()
    files = get_all_smt_files_recursively("/home/histfuzz/seeds")
    for file in files:
        run_solver(z3_bin, file)
        run_solver(cvc5_bin, file)
    fastcov = subprocess.Popen("fastcov -l -o coverage-seed100.info", shell=True, cwd=z3_folder, stdout=subprocess.DEVNULL)
    coverage = subprocess.Popen("make coverage; mv coverage.info coverage-seed100.info", shell=True, cwd=cvc5_folder, stdout=subprocess.DEVNULL)
    fastcov.wait()
    coverage.wait()


def run_tool_and_record_coverage(fuzzer, z3_folder, cvc5_folder, times=1, cores=1):
    # Open files to record code coverage
    with open(z3_folder + "/coverage.txt", "a") as f1:
        f1.write("\n{} code coverage:\n".format(fuzzer))
    with open(cvc5_folder + "/coverage.txt", "a") as f2:
        f2.write("\n{} code coverage:\n".format(fuzzer))
        
    # Initialize commands for clearing previous coverage data
    z3_clear_data = "lcov -d ./ -z"
    cvc_clear_data = "make coverage-reset"

    if fuzzer in ["opfuzz", "typefuzz", "yinyang"]:
        # Get all SMT files recursively from a specific directory
        files = get_all_smt_files_recursively("/home/histfuzz/seeds")
    for time in range(times):
        # Clear previous coverage data for Z3 and CVC5
        p1 = subprocess.Popen(z3_clear_data, shell=True, cwd=z3_folder, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        p2 = subprocess.Popen(cvc_clear_data, shell=True, cwd=cvc5_folder, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        p1.wait()
        p2.wait()
        if fuzzer in ["opfuzz", "typefuzz", "yinyang"]:
            if fuzzer in ["opfuzz", "typefuzz"]:
                # Run fuzzing tools in parallel with multiprocessing.Pool
                pool = multiprocessing.Pool(processes=cores)
                for file in files:
                    if fuzzer == "opfuzz":
                        pool.apply_async(run_op, (file,))
                    elif fuzzer == "typefuzz":
                        pool.apply_async(run_type, (file,))
            if fuzzer == "yinyang":
                # Run Yinyang fuzzer 100 times with random SMT files
                pool = multiprocessing.Pool(processes=cores)
                for i in range(100):
                    pool.apply_async(run_yinyang, (random.choice(files), random.choice(files)))

            # Wait for all processes to complete
            pool.close()
            pool.join()
        if fuzzer == "storm":
            # Run Storm fuzzer
            p1 = subprocess.Popen("""/bin/bash -c "source venv/bin/activate; storm --solver=z3 --solverbin={} --benchmark=/home/histfuzz/seeds --theory=LIA" """.format(z3_bin), shell=True, cwd="/home/histfuzz/baselines/storm", stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
            p1.wait()
            p2 = subprocess.Popen("""/bin/bash -c "source venv/bin/activate; storm --solver=cvc4 --solverbin={} --benchmark=/home/histfuzz/seeds --theory=LIA" """.format(cvc5_bin), shell=True, cwd="/home/histfuzz/baselines/storm", stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
            p2.wait()
        if fuzzer == "histfuzz":
            # Run HistFuzz 
            pro = run_histfuzz()
            pro.wait()

        # Record code coverage using fastcov and lcov
        fastcov = subprocess.Popen("fastcov -l -o cover-run" + str(time) + ".info; lcov -a cover-run" + str(time) + ".info" + " -a coverage-seed100.info -o output.txt >> coverage.txt", shell=True, cwd=z3_folder, stdout=subprocess.DEVNULL)
        coverage = subprocess.Popen("make coverage; lcov -a coverage.info -a coverage-seed100.info -o output.info >> coverage.txt", shell=True, cwd=cvc5_folder, stdout=subprocess.DEVNULL)
        fastcov.wait()
        coverage.wait()


def run_histfuzz():
    command = "/home/histfuzz/bin/histfuzz --solver1=z3 --solverbin1={} --solver2=cvc5 --solverbin2={} --incremental --option=default --mutant=1000".format(z3_bin, cvc5_bin)
    p = subprocess.Popen(command, shell=True, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
    return p


def run_op(file):
    command = "/home/histfuzz/baselines/yinyang/bin/opfuzz  -i 1" + """ "{} ;{} " """.format(z3_bin, cvc5_bin) + file
    p = subprocess.Popen(command, shell=True, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
    p.wait()
    return

def run_type(file):
    command = "/home/histfuzz/baselines/yinyang/bin/typefuzz -i 1" + """ "{} model_validate=true;{} --check-models --strings-exp " """.format(z3_bin, cvc5_bin) + file
    p = subprocess.Popen(command, shell=True, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
    p.wait()
    return


def run_yinyang(file1, file2):
    command = "/home/histfuzz/baselines/yinyang/bin/yinyang -i 1 -o sat" + """ "{} model_validate=true;{} --check-models --strings-exp " """.format(z3_bin, cvc5_bin) + file1 + " " + file2
    p = subprocess.Popen(command, shell=True, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
    p.wait()
    return


if __name__ == "__main__":

    print("SAMPLE FILES")
    file_list = get_all_smt_files_recursively("/home/histfuzz/bug_triggering_formulas")
    classify_seeds(file_list, z3_bin, 100)
    print("ACHIEVE SEEDS' CODE COVERAGE")
    run_seeds_coverage(z3_folder, cvc5_folder)
    print("ACHIEVE CODE COVERAGE")
    for fuzzer in ["opfuzz", "typefuzz", "yinyang", "storm", "histfuzz"]:
        print("obtain {} code coverage".format(fuzzer))
        run_tool_and_record_coverage(fuzzer, z3_folder, cvc5_folder)
    if not os.path.exists("/home/histfuzz/reproduce/result"):
        os.makedirs("/home/histfuzz/reproduce/result")
    current_time = time.strftime("%Y-%m-%d-%H-%M", time.localtime())

    shutil.move("{}/coverage.txt".format(z3_folder), "/home/histfuzz/reproduce/result/z3-{}.txt".format(current_time))
    shutil.move("{}/coverage.txt".format(cvc5_folder), "/home/histfuzz/reproduce/result/cvc5-{}.txt".format(current_time))

    if os.path.exists("/home/histfuzz/reproduce/bugs"):
        shutil.rmtree("/home/histfuzz/reproduce/bugs")
    if os.path.exists("/home/histfuzz/reproduce/logs"):
        shutil.rmtree("/home/histfuzz/reproduce/logs")
    if os.path.exists("/home/histfuzz/reproduce/scratch"):
        shutil.rmtree("/home/histfuzz/reproduce/scratch")