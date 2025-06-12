
import os
import subprocess
import argparse

YINYANG_BIN = "./yinyang/bin/yinyang"
HISTFUZZ_BIN = "./histfuzz/bin/histfuzz"


def get_smt_files_list_within_size(path_to_directory, size):
    size_kb = size * 1024
    return [
        os.path.join(r, file)
        for r, _, f in os.walk(path_to_directory)
        for file in f
        if file.endswith(('.smt2', '.fuzz'))
        and "_tactic" not in file
        and ".smt20" not in file
        and os.path.getsize(os.path.join(r, file)) <= size_kb
    ]

def get_all_smt_files_recursively(path_to_directory):
    return [
        os.path.join(r, file)
        for r, _, f in os.walk(path_to_directory)
        for file in f
        if file.endswith(('.smt2', '.fuzz')) 
        and "_tactic" not in file
        and ".smt20" not in file
    ]


def run_solver(solver_bin, smt_file):
    options = {
        "z3": "",
        "cvc5": ""
    }
    command = f"timeout 10s {solver_bin} {options.get(solver_bin, '')} {smt_file}"
    p = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    p.wait()
    return p.stdout.read().decode().strip()  # return the result if needed



def run_seeds_coverage(z3_folder, cvc5_folder, seed_dir, file_name, idx=0):
    def clear_coverage_data(folder, command):
        p = subprocess.Popen(command, shell=True, cwd=folder, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        p.wait()

    clear_coverage_data(z3_folder, "lcov -d ./ -z")
    clear_coverage_data(cvc5_folder, "make coverage-reset")

    files = get_all_smt_files_recursively(seed_dir)
    for file in files:
        run_solver(z3_bin, file)
        run_solver(cvc5_bin, file)

    subprocess.run(f"fastcov -l -o coverage-{file_name}-{idx}.info", shell=True, cwd=z3_folder, stdout=subprocess.DEVNULL)
    subprocess.run(f"make coverage; mv coverage.info coverage-{file_name}-{idx}.info", shell=True, cwd=cvc5_folder, stdout=subprocess.DEVNULL)



def run_tool_and_record_coverage(fuzzer, z3_folder, cvc5_folder, z3_bin, cvc5_bin, seed_dir, times=1, cores=1):
    coverage_file_z3 = os.path.join(z3_folder, "coverage.txt")
    coverage_file_cvc5 = os.path.join(cvc5_folder, "coverage.txt")

    with open(coverage_file_z3, "a") as f1, open(coverage_file_cvc5, "a") as f2:
        f1.write(f"\n{fuzzer} code coverage:\n")
        f2.write(f"\n{fuzzer} code coverage:\n")
        
    for ctime in range(times):
        print(f"Running {fuzzer} for the {ctime} time")
        subprocess.run("lcov -d ./ -z", shell=True, cwd=z3_folder, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        subprocess.run("make coverage-reset", shell=True, cwd=cvc5_folder, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        
        if fuzzer == "yinyang":
            run_yinyang(seed_dir)

        if fuzzer == "storm":
            for solver, bin in [("z3", z3_bin), ("cvc4", cvc5_bin)]:
                subprocess.run(
                    f'/bin/bash -c "source venv/bin/activate; storm --solver={solver} --solverbin={bin} --benchmark=/root/ase-exp/tools/HistFuzz/seeds --theory=LIA"',
                    shell=True, cwd="./storm", stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL
                )

        if fuzzer == "histfuzz":
            run_histfuzz().wait()

        if fuzzer == "octopus":
            subprocess.run(f"timeout 1h python3 ../octopus/__main__.py --solver1=z3 --solverbin1={z3_bin} --solver2=cvc5 --solverbin2={cvc5_bin} --benchmark={seed_dir} --cores={cores}", shell=True,  stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)

        subprocess.run(f"fastcov -l -o coverage-{fuzzer}-run{ctime}.info; lcov -a coverage-{fuzzer}-run{ctime}.info -o output.txt >> {coverage_file_z3}", shell=True, cwd=z3_folder, stdout=subprocess.DEVNULL)
        subprocess.run(f"make coverage; lcov -a coverage.info -o output.info >> {coverage_file_cvc5}", shell=True, cwd=cvc5_folder, stdout=subprocess.DEVNULL)


def run_histfuzz():
    command = f"timeout 1h {HISTFUZZ_BIN} --solver1=z3 --solverbin1={z3_bin} --solver2=cvc5 --solverbin2={cvc5_bin} --option=default"
    return subprocess.Popen(command, shell=True, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)


def run_yinyang(seed_dir, oracle="sat"):
    command = f"timeout 1h {YINYANG_BIN} -b ./yinyang -o {oracle} '{z3_bin}; {cvc5_bin}' {seed_dir}"
    subprocess.run(command, shell=True, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)


def print_code_coverage(info_file, output_file, solver_folder):
    command = f"lcov -a {info_file} -o temp.info >> {output_file}"
    subprocess.run(command, shell=True, cwd=solver_folder, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)




if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='This script reproduces the experiments regarding the code coverage of the solvers')
    parser.add_argument('solver1_build_dir', type=str, help='The directory of the first solver')
    parser.add_argument('solver2_build_dir', type=str, help='The directory of the second solver')
    parser.add_argument('solver1_bin', type=str, help='The path to the first solver binary')
    parser.add_argument('solver2_bin', type=str, help='The path to the second solver binary')
    parser.add_argument('seeds', type=str, help='The directory of the seeds')
    parser.add_argument('--times', type=int, help='The number of times to run the experiment', default=1)
    args = parser.parse_args()

    for fuzzer in ["yinyang", "storm", "histfuzz", "octopus"]:
        print("obtain {} code coverage".format(fuzzer))
        if "z3" in args.solver1_bin or "z3" in args.solver1_build_dir:
            z3_bin = args.solver1_bin
            cvc5_bin = args.solver2_bin
            z3_folder = args.solver1_build_dir
            cvc5_folder = args.solver2_build_dir
        else:
            z3_bin = args.solver2_bin
            cvc5_bin = args.solver1_bin
            z3_folder = args.solver2_build_dir
            cvc5_folder = args.solver1_build_dir
        run_tool_and_record_coverage(fuzzer, z3_folder, cvc5_folder, z3_bin, cvc5_bin, args.seeds, times=args.times, cores=1)