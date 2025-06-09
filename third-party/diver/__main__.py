import os, sys
import multiprocessing
import inspect
import random
import shutil
import datetime
import string
import logging
import numpy as np
import re
import math
import time
import unittest
import pathlib
import cvc5
from cvc5 import Kind
from z3 import *
from queue import PriorityQueue
from termcolor import colored
from parser.smt_parser import *
from utils.file_tool import *
from utils.solver import *
from utils.arg_parser import *
from utils.debug import *
from utils.options import *
from analyzer.analysis import *
from logging.config import dictConfig
from fuzzer.generator import *
from analyzer.pre_analyzer import *

dictConfig({
    'version': 1,
    'formatters': {
        'default': {
            'format': '[%(asctime)s] %(message)s',
        }
    },
    'handlers': {
        'file': {
            'level': 'DEBUG',
            'class': 'logging.FileHandler',
            'filename': 'running_data.log',
            'formatter': 'default',
        },
    },
    'root': {
        'level': 'DEBUG',
        'handlers': ['file']
    }
})

manager = multiprocessing.Manager()
final_list = manager.list()


def bug_copy(core, s_name, m_name, tmp_path, solver, SEED, seed, bug_type, message=None, debugging_info=None):
    now = time.localtime()
    t = "%04d/%02d/%02d %02d:%02d:%02d" % (now.tm_year, now.tm_mon, now.tm_mday, now.tm_hour, now.tm_min, now.tm_sec)
    logging.debug("File: {} -> {}'s {}".format(m_name, solver, bug_type))
    print(
        colored("[{}] [core-{}] ({},{}) SMT Solver({})=>Bug Type:{}".format(t, core, s_name, m_name, solver, bug_type),
                'red'))
    bug_dir = os.path.join(os.getcwd(), "bug_dir")
    bug_dir = os.path.join(bug_dir, solver)
    bug_file_dir = os.path.join(bug_dir, s_name + "_" + str(SEED))
    create_bug_dir(bug_file_dir)

    mutant = os.path.join(tmp_path, m_name)
    shutil.copy2(seed, bug_file_dir)
    shutil.move(mutant, bug_file_dir)

    if (message is not None) and (len(message) != 0):
        f = open(bug_file_dir + "/" + m_name, mode='a', encoding='utf-8')
        f.write(";;" + message + "\n")
        f.close()

    if debugging_info is not None:
        f = open(bug_file_dir + "/" + m_name, mode='a', encoding='utf-8')
        node_info = ";; Node : {} Node_Score : {}".format(debugging_info[0], debugging_info[1])
        p_info = ";; p^l : {}".format(debugging_info[2])
        q_info = ";; q^l : {}".format(debugging_info[3])
        f.write(node_info + "\n")
        f.write(p_info + "\n")
        f.write(q_info + "\n")
        f.close()
    return


def run_solver_in_thread(core, seed, s_name, mutant, m_name, solver, s_bin, path, timeout, opt, SEED, logic, diver_mode,
                         debugging_info=None):
    try:
        message, res = run_solver(mutant, solver, s_bin, timeout, opt)
        if res == "unsat":
            if diver_mode == "nooracle":
                return res
            if solver in ["cvc", "z3"]:
                bug_msg = ""
                if len(opt) != 0:
                    bug_msg = "[option] : "
                    for o in opt:
                        bug_msg += o + " "
                bug_msg += " => [Bug Type] : Refutation Soundness in " + solver
                bug_copy(core, s_name, m_name, path, solver + "_soundness", SEED, seed, "Soundness Bug", bug_msg,
                         debugging_info)
                return "unsat"
            else:
                bug_msg = ""
                if len(opt) != 0:
                    bug_msg = "[option] : "
                    for o in opt:
                        bug_msg += o + " "
                bug_msg += " => [Bug Type] : Refutation Soundness in " + solver
                bug_copy(core, s_name, m_name, path, solver + "_soundness", SEED, seed, "Soundness Bug", bug_msg,
                         debugging_info)
                return "unsat"
            return "sat"
        elif res == "crash" and ("ASSERTION" in message or "an invalid model was generated" in message):
            bug_msg = ""
            if len(opt) != 0:
                bug_msg = "[option] : "
                for o in opt:
                    bug_msg += o + " "

            bug_msg += " => [Bug Type] : Invalid Model in " + solver + " [Error Message] : " + message
            bug_copy(core, s_name, m_name, path, solver + "_invalid", SEED, seed, "Invalid Model Bug", bug_msg,
                     debugging_info)
            res = "invalid"
            return res
        elif res == "crash":
            bug_msg = ""
            if len(opt) != 0:
                bug_msg = "[option] : "
                for o in opt:
                    bug_msg += o + " "
            bug_msg += " => [Bug Type] : Crash in " + solver + " [Error Message] : " + message
            bug_copy(core, s_name, m_name, path, solver + "_crash", SEED, seed, "Crash Bug", bug_msg, debugging_info)
            return res
        else:
            pass
        return res
    except Exception as e:
        trace = inspect.trace()
        fn = trace[-1].filename
        lineno = trace[-1].lineno
        print("Runtime error at %s:%s" % (fn, lineno), flush=True)
        print("msg: " + str(e), flush=True)
        return "error"


@trace
def run_diver_dreal(arg, benchmark, core, wait, SEED):
    mutant_root = os.path.join(os.getcwd(), "test_suit")
    mutant_path = os.path.join(os.path.join(mutant_root, arg["server"], "core_" + str(core)))
    create_core_dir(mutant_root, arg["server"], core)

    seed_count = 0

    result = {"sat": 0, "unsat": 0, "crash": 0, "invalid": 0, "error": 0, "timeout": 0, "unknown": 0}

    solver_time = 0.0
    unsat_time = 0.0
    sat_time = 0.0
    gen_time = 0.0
    judge_time = 0.0

    fuzzer_stat = [0.0 for i in range(5)]
    fuzzer_stat[0] = int(fuzzer_stat[0])

    total_start = time.time()
    iters = arg["mutants"]

    while len(benchmark) != 0:
        try:
            seed = random.choice(benchmark)
            benchmark.remove(seed)

            file_name = get_name(seed)
            file_size = pathlib.Path(seed).stat().st_size
            if file_size >= 200000:
                continue

            if arg["opt"]:
                optimize_smt2(seed)

            ### Pre Analysis Phase
            print("[core-{}] Run testing SMT Solver with formula - {}".format(core, seed))

            ## (1) Get Model
            var, logic_ = get_variable(seed)

            m, res = run_solver(seed, arg["solver"], arg["solverbin"], arg["timeout"], [], var)
            if res != "sat" or m is None:
                print("[core-{}] GetModel Fail! -> {} (seed: {})".format(core, res, seed))
                continue

            ## (2) PREANALYSIS
            C = preprocess(seed, var, m, arg["logic"])
            if C["spc"] is None:
                print("[core-{}] PreAnalysis Fail!")
                continue

            score, p_score = get_score(C["spc"], arg["solver"], m)
            nodes = list(score.keys())
            l_score = list(score.values())

            if len(nodes) == 0:
                continue

            seed_info = {"seed_var": C["var"], "seed_const": C["const"], "seed_model": m, "logic": arg["logic"]}
            solver_data = {"data": [C["cal"], C["parent"], C["tree"]], "model": m, "solver": arg["solver"], "vars": var}

            iter = 0
            ast = C["ast"]
        except KeyboardInterrupt:
            return
        except Exception as e:
            print("Line 183 : Error {}".format(e))
            continue
        while iter < iters:
            try:
                node = (random.choices(nodes, weights=l_score, k=1)[0]) if arg["mode"] != "noweight" else (
                    random.choice(nodes))

                term = C["term"][node]
                cond = C["spc"][node]
                if not (cond[2]):
                    continue

                mutate_info = [node, term, cond[1]]
                line = node.split('_')[0]

                formula_info = {"line": line, "ast": ast[int(line)][2]}
                file_info = {"file_path": seed, "mutant_path": mutant_path, "iter": iter}

                generator = MutantGenerator(seed_info, solver_data, formula_info, file_info, mutate_info,
                                            arg["max_depth"], arg["mode"], arg["experiment"])

                mutant, trial, q, jdt, gnt = generator.gen_mutant()
                judge_time += jdt
                gen_time += gnt

                if mutant == "Fail":
                    fuzzer_stat[1] += trial
                    continue

                mutant_name = mutant.split('/')[-1]
                solver_start = time.time()
                if arg["debug"]:
                    debugging_info = [node, p_score[node], term, q]
                    res = run_solver_in_thread(core, seed, file_name, mutant, mutant_name, arg["solver"],
                                               arg["solverbin"], mutant_path, arg["timeout"], arg["option"], SEED,
                                               arg["logic"], arg["mode"], debugging_info)
                else:
                    res = run_solver_in_thread(core, seed, file_name, mutant, mutant_name, arg["solver"],
                                               arg["solverbin"], mutant_path, arg["timeout"], arg["option"], SEED,
                                               arg["logic"], arg["mode"])
                solt = time.time() - solver_start
                if arg["mode"] == "nooracle":
                    if res == "sat" or res == "invalid":
                        sat_time += solt
                    elif res == "unsat":
                        unsat_time += solt
                    solver_time += solt

                else:
                    solver_time += solt  # testing time

                fuzzer_stat[0] += 1
                iter += 1
                fuzzer_stat[1] += trial
                result[res] += 1

                if res == "sat":
                    tmp_name = file_name.split('.')[0]
                    shutil.copy2(mutant, "./tmp_benchmark/core_" + str(core) + "/" + tmp_name + "_mutant_" + str(
                        iter) + ".smt2")
                    benchmark.append(
                        "./tmp_benchmark/core_" + str(core) + "/" + tmp_name + "_mutant_" + str(iter) + ".smt2")

                logging.debug(
                    "#Mutant {} #Gen {} Res {} ST {} UT {} TT {} GT {} JT {}".format(fuzzer_stat[0], fuzzer_stat[1],
                                                                                     res, sat_time, unsat_time,
                                                                                     solver_time, gen_time, judge_time))

            except KeyboardInterrupt:
                return
            except Exception as e:
                trace = inspect.trace()
                fn = trace[-1].filename
                lineno = trace[-1].lineno
                print(lineno, e, fn)
                continue

    return


@trace
def run_diver(arg, benchmark, core, wait, SEED):
    mutant_root = os.path.join(os.getcwd(), "test_suit")
    mutant_path = os.path.join(os.path.join(mutant_root, arg["server"], "core_" + str(core)))
    create_core_dir(mutant_root, arg["server"], core)

    seed_count = 0

    result = {"sat": 0, "unsat": 0, "crash": 0, "invalid": 0, "error": 0, "timeout": 0, "unknown": 0}
    ##### 
    solver_time = 0.0
    unsat_time = 0.0
    sat_time = 0.0
    gen_time = 0.0
    judge_time = 0.0

    fuzzer_stat = [0.0 for i in range(5)]  # succ, fail, end-to-end, solver, gen
    fuzzer_stat[0] = int(fuzzer_stat[0])

    total_start = time.time()
    iters = arg["mutants"]
    while len(benchmark) != 0:
        try:
            seed = random.choice(benchmark)
            benchmark.remove(seed)

            file_name = get_name(seed)
            file_size = pathlib.Path(seed).stat().st_size
            if file_size >= 200000:
                continue

            if arg["opt"]:
                optimize_smt2(seed)

            ### Pre Analysis Phase
            print("[core-{}] Run testing SMT Solver with formula - {}".format(core, seed))

            var, logic_ = get_variable(seed)
            ast = transform_smt_to_ast(seed)

            ## (1) Get Model
            solver_data, model = get_model(seed, ast, arg["solver_api"], var, arg["logic"])
            if solver_data is None:
                print("[core-{}] GetModel Fail! -> {} (seed: {})".format(core, model, seed))
                continue

            ## (2) PREANALYSIS
            analyzer = PreAnalyzer(seed, ast, var, solver_data["model"], arg["logic"], solver_data["vars"],
                                   arg["solver_api"])
            status, analysis = analyzer.pre_analysis()

            if status == "Fail":
                print("[core-{}] PreAnalysis Fail!")
                continue

            constraints = analysis["constraints"]
            variables = analysis["var"]
            constants = analysis["const"]
            terms = analysis["term"]

            score, p_score = get_score(constraints, arg["solver_api"], solver_data["model"])
            nodes = list(score.keys())

            l_score = list(score.values())

            seed_info = {"seed_var": variables, "seed_const": constants, "seed_model": model, "logic": arg["logic"]}
            iter = 0
            while iter < iters:
                try:
                    node = (random.choices(nodes, weights=l_score, k=1)[0]) if arg["mode"] != "noweight" else (
                        random.choice(nodes))

                    term = terms[node]
                    constraint = constraints[node]

                    if not constraint[3]:
                        # selects node which cannot mutate.
                        continue

                    mutate_info = [node, term, constraint[1]]
                    line = node.split('_')[0]

                    formula_info = {"line": line, "ast": ast[int(line)][2]}
                    file_info = {"file_path": seed, "mutant_path": mutant_path, "iter": iter}

                    generator = MutantGenerator(seed_info, solver_data, formula_info, file_info, mutate_info,
                                                arg["max_depth"], arg["mode"], arg["experiment"])

                    mutant, trial, q, jdt, gnt = generator.gen_mutant()
                    judge_time += jdt
                    gen_time += gnt

                    if mutant == "Fail":
                        fuzzer_stat[1] += trial
                        continue
                    mutant_name = mutant.split('/')[-1]
                    solver_start = time.time()
                    if arg["debug"]:
                        debugging_info = [node, p_score[node], term, q]
                        res = run_solver_in_thread(core, seed, file_name, mutant, mutant_name, arg["solver"],
                                                   arg["solverbin"], mutant_path, arg["timeout"], arg["option"], SEED,
                                                   arg["logic"], arg["mode"], debugging_info)
                    else:
                        res = run_solver_in_thread(core, seed, file_name, mutant, mutant_name, arg["solver"],
                                                   arg["solverbin"], mutant_path, arg["timeout"], arg["option"], SEED,
                                                   arg["logic"], arg["mode"])
                    solt = time.time() - solver_start
                    if arg["mode"] == "nooracle":
                        if res == "sat" or res == "invalid":
                            sat_time += solt
                        elif res == "unsat":
                            unsat_time += solt
                        solver_time += solt
                    else:
                        solver_time += solt  # testing time

                    fuzzer_stat[0] += 1
                    iter += 1
                    fuzzer_stat[1] += trial
                    result[res] += 1

                    if res == "sat":
                        tmp_name = file_name.split('.')[0]
                        shutil.copy2(mutant, "./tmp_benchmark/core_" + str(core) + "/" + tmp_name + "_mutant_" + str(
                            iter) + ".smt2")
                        benchmark.append(
                            "./tmp_benchmark/core_" + str(core) + "/" + tmp_name + "_mutant_" + str(iter) + ".smt2")

                    logging.debug(
                        "#Mutant {} #Gen {} Res {} ST {} UT {} TT {} GT {} JT {}".format(fuzzer_stat[0], fuzzer_stat[1],
                                                                                         res, sat_time, unsat_time,
                                                                                         solver_time, gen_time,
                                                                                         judge_time))
                except Exception as e:
                    trace = inspect.trace()
                    fn = trace[-1].filename
                    lineno = trace[-1].lineno
                    print(lineno, e, fn)
                    continue
        except Exception as e:
            print("Line 183 : Error {}".format(e))
            continue
        # logging.debug("[State : Result of Mutant ] sat: {}, unsat: {}, unknown: {}, invalid: {}, crash: {}, error: {}, timeout: {}".format(result["sat"],result["unsat"],result["unknown"],result["invalid"],result["crash"],result["error"],result["timeout"]))
    return


@trace
def main():
    args = ArgParser()
    args.parse_arguments(argparse.ArgumentParser())
    parsedArg = args.get_arguments()
    SEED = parsedArg["seed"]
    random.seed(SEED)
    try:
        cores = int(parsedArg["cores"])
        benchmark = distribute_benchmark(parsedArg["benchmark"], cores)

        # multi processing
        procs = []
        logging.debug("Start!!!!")
        for i in range(cores):
            core = str(i)
            wait = int(core)
            # logging.debug("core-{} will generate mutant formulas using #{} seed formulas".format(core,len(benchmark[i])))
            if parsedArg["solver"] in ["z3", "cvc"]:
                process = multiprocessing.Process(target=run_diver, args=(parsedArg, benchmark[i], core, wait, SEED))
            else:
                process = multiprocessing.Process(target=run_diver_dreal,
                                                  args=(parsedArg, benchmark[i], core, wait, SEED))
            process.deamon = True
            SEED = str((int(SEED) + 1))
            procs.append(process)
            process.start()

        return 0
    except KeyboardInterrupt:
        print("terminate Diver")
        for proc in procs:
            if proc.is_alive():
                proc.terminate()
        print("\nGood Bye!\n")
        return
    except Exception as e:
        trace = inspect.trace()
        fn = trace[-1].filename
        lineno = trace[-1].lineno
        print("Runtime error at %s:%s" % (fn, lineno), flush=True)
        print("msg: " + str(e), flush=True)
        print("\nGood Bye!\n")


if __name__ == '__main__':
    sys.setrecursionlimit(10000000)
    main()
