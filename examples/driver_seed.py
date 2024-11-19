import argparse
import glob
import hashlib
import inspect
import json
import logging
import os
import random
import shutil
import signal
# import statistics
import statistics as st
import subprocess
import sys
import time
from multiprocessing.pool import ThreadPool
from threading import Timer

import tqdm

from mutators.opt_mutator import StringMutation

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
parentdir = os.path.dirname(currentdir)

m_generator = parentdir + '/smtfuzz/smtfuzz.py'
m_bet_mutator = currentdir + '/mutators/bet_mutator.py'

m_test_invalid_model = True
m_has_z3py = True

try:
    from mutators.bet_mutator import Z3Mutation
except Exception as e:
    print(e)
    print("No z3py, will use StrMut or TyMut")
    m_has_z3py = False


class Statistic:
    def __init__(self):
        print("Sparrow is running:")
        self.starttime = time.time()
        self.seeds = 0
        self.mutants = 0
        self.error = 0
        self.soundness = 0
        self.timeout = 0
        self.solving_time = 0
        self.mutation_time = 0
        self.ignored = 0
        self.profile_data = []

    def printbar(self):
        bar = "[time:%ds, #mutant:%d, #seed:%d, #crash:%d, #unsound:%d, #timeout:%d, #ignored:%d]" \
              % (time.time() - self.starttime, self.mutants, self.seeds, self.error, self.soundness, self.timeout,
                 self.ignored)
        print(bar, end="\r", flush=True)

    def printsum(self):
        summary = """

Summary:
Passed time: %ds
Generated mutants: %d
Used seeds: %d
Crash issues: %d
Unsound issues: %d
Timeout cases: %d
Ignored issues: %d
""" \
                  % (time.time() - self.starttime, self.mutants, self.seeds, self.error, self.soundness, self.timeout,
                     self.ignored)
        print(summary, end="\n", flush=True)


parser = argparse.ArgumentParser()
parser.add_argument('--input', dest='input', type=str)
parser.add_argument('--output', dest='output', default='~/tmp/res/', type=str)
parser.add_argument('--timeout', dest='timeout', default=10, type=int, help="timeout for each solving")
parser.add_argument('--count', dest='count', default=50, type=int, help="counts for each combination")
parser.add_argument('--workers', dest='workers', default=1, type=int, help="num threads")

parser.add_argument('--solvermode', dest='solvermode', default='default', type=str)
parser.add_argument('--logicmode', dest='logicmode', default='default', type=str)

parser.add_argument('--config', dest='config', default='no', type=str)
parser.add_argument('--seed', dest='seed', default='no', type=str)
parser.add_argument('--optfuzz', dest='optfuzz', default='no', type=str)

parser.add_argument('--diff', dest='diff', default='no', type=str)
parser.add_argument('--perf', dest='perf', default='no', type=str)
parser.add_argument('--nomut', dest='nomut', default='no', type=str)
parser.add_argument('--solver', dest='solver', default='all', type=str)
parser.add_argument('--solvers', dest='solvers', default='no', type=str)

# for evaluation
parser.add_argument('--formula_injection', dest='formula_injection', default='none', type=str)
parser.add_argument("-p", "--profile", help="profile the speed of mutation",
                    action="store_true")

parser.add_argument("-v", "--verbose", help="increase output verbosity",
                    action="store_true")

args = parser.parse_args()
if args.verbose:
    logging.basicConfig(level=logging.DEBUG)

in_dir = args.input
out_dir = args.output
timeout = args.timeout
count = args.count

g_statistic = None
if args.workers == 1:
    g_statistic = Statistic()

shutil.rmtree(out_dir)
os.mkdir(out_dir)

crashes = out_dir + '/crash'
inputs = out_dir + '/input'
os.mkdir(crashes)
os.mkdir(inputs)

black_list = []
black_list_files = ['../black_list_cvc4_new', '../black_list_z3', '../black_list_open', '../black_list_yices2']
for f in black_list_files:
    bf = open(f, 'r')
    for l in bf:
        black_list.append(l.replace("\n", ""))
    bf.close()


def terminate(process, is_timeout):
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as e:
            # pass
            print("error for interrupting")


def try_z3_mutate(file, output):
    if not m_has_z3py:
        return False  # z3py
    ret = True
    cmd = ['python3', m_bet_mutator, "--input", file, "--output", output]
    if args.optfuzz == "yes" and args.diff == "no":
        if args.solver == "z3":
            cmd.append("--optionmode")
            cmd.append("z3")
        elif args.solver == "cvc5":
            cmd.append("--optionmode")
            cmd.append("cvc4")

    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    is_timeout = [False]
    timer = Timer(5, terminate, args=[p, is_timeout])
    timer.start()
    out = p.stdout.readlines()
    out = ' '.join([str(element.decode('UTF-8')) for element in out])
    # print(out)
    if is_timeout[0]:  # do not add timeout case
        logging.debug("Timeout when using z3py for mutation")
        ret = False
    elif "error" in out or "Segment" in out or "Exception" in out:
        logging.debug("Error when usng z3py for mutation!")
        logging.debug(out)
        ret = False

    p.stdout.close()
    timer.cancel()
    return ret


def profile(pack):
    solver = pack[0]
    tmp_file = pack[1]
    outdir = pack[2]

    if os.stat(tmp_file).st_size == 0:
        # print("tmp file empty")
        return
    try:
        if g_statistic:
            g_statistic.seeds += 1
            g_statistic.printbar()
        logging.debug("Start to mutate")
        idt = 0
        counter = hashlib.md5(tmp_file.encode('utf-8')).hexdigest()
        name = '/muta_input-' + str(idt) + "_" + str(counter)[0:6] + '_'
        gene = StringMutation(tmp_file)

        xxxname = name
        for i in range(args.count):
            tmp_start = time.time()
            tmp_file_mut = inputs + name + str(i) + ".smt2"
            xxxname = name + str(i) + ".smt2"
            try:
                with open(tmp_file_mut, 'w') as mut:
                    if gene.generate(tmp_file_mut):
                        logging.debug("mutate success")
                    else:
                        if os.path.isfile(tmp_file_mut):
                            os.remove(tmp_file_mut)
                        break
            except Exception as file_e:
                print(file_e)
                if os.path.isfile(tmp_file_mut):
                    os.remove(tmp_file_mut)
                continue
            tmp_end = time.time()
            if g_statistic:
                g_statistic.profile_data.append(tmp_end - tmp_start)
                g_statistic.mutants += 1
    except Exception as ee:
        print(ee)


def worker(pack):
    solver = pack[0]
    tmp_file = pack[1]
    outdir = pack[2]

    if os.stat(tmp_file).st_size == 0:
        # print("tmp file empty")
        return

    # Load the configuration file
    with open('test_config.json', 'r') as file:
        config = json.load(file)

    def get_solver_path(solver: str):
        return config.get(solver, solver)

    cmd_tool = []
    to_test = None
    if solver == 'yices':
        to_test = get_solver_path("yices")
    elif solver == 'cvc5':
        to_test = get_solver_path("cvc5")
    elif solver == 'z3':
        to_test = get_solver_path("z3")
    elif solver == 'open':
        to_test = get_solver_path("open")
    elif solver == 'pol':
        to_test = get_solver_path("pol")
    else:
        to_test = solver  # allow for specifying the solver bin in cmd

    for cc in to_test.split(' '):  # currently, choose the first tool
        cmd_tool.append(cc)

    if 'cvc' in to_test:
        cmd_tool.append('--quiet')
        if args.solvermode == 'unsat_core':
            cmd_tool.append('--check-unsat-cores')
        if not args.solvermode == 'sygus':
            cmd_tool.append('--incremental')
        cmd_tool.append('--check-models')
        # cmd_tool.append('--strings-exp')
    if 'yice' in to_test or 'boolec' in to_test:
        cmd_tool.append('--incremental')

    # if 'z3' in to_test:
    #    cmd_tool.append('tactic.default_tactic=smt')
    #    cmd_tool.append('sat.euf=true')

    try:
        cmd_seed = cmd_tool
        cmd_seed.append(tmp_file)
        logging.debug("Seed res: ")
        logging.debug(cmd_seed)
        env = os.environ.copy()
        if 'cvc' in to_test or 'open' in to_test:  #
            env["ASAN_OPTIONS"] = "log_path=stdout:" + \
                                  env.get("ASAN_OPTIONS", "")
            env["ASAN_OPTIONS"] += "detect_leaks=0"

        # t_start = time.time()
        ptool = subprocess.Popen(cmd_seed, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
        is_timeout = [False]
        timertool = Timer(10, terminate, args=[ptool, is_timeout])
        timertool.start()
        out_seed = ptool.stdout.readlines()
        out_seed = ' '.join([str(element.decode('UTF-8')) for element in out_seed])
        logging.debug(out_seed)

        if is_timeout[0]:  # do not add timeout case
            ptool.stdout.close()
            timertool.cancel()
            return
        elif "unknown" in out_seed or "error" in out_seed or "Error" in out_seed:
            ptool.stdout.close()
            timertool.cancel()
            return
        elif "Santi" in out_seed or 'ASSERTION' in out_seed or 'Assert' in out_seed or 'Fat' in out_seed or (
                m_test_invalid_model and 'invalid mo' in out_seed):
            err_flag = True
            for item in black_list:
                if not item:
                    continue  # in case there is empty line!
                if item in out_seed:
                    err_flag = False
                    break
            if err_flag:
                print("find error!")
                print("seed cmd: ", cmd_seed)
                print("seed res: ", out_seed)
                print("seed: ", tmp_file)
                shutil.copy(tmp_file, outdir + "/crash")
                return

        ptool.stdout.close()
        timertool.cancel()

        if g_statistic:
            # g_statistic.solving_time = time.time() - t_start
            g_statistic.seeds += 1

        if args.nomut == "yes":
            return

        logging.debug("Start to mutate")

        solver_opts = [" "]
        if args.optfuzz == 'yes':
            if args.solver == 'z3':
                # solver_opts = ["NA", "rewriter.flat=false", "smt.arith.solver=2"]
                solver_opts = ["NA"]
            elif args.solver == 'cvc5':
                solver_opts = ["NA", "--cegqi", "--strings-exp", "--fmf-fun"]
                # solver_opts = ["NA"]
            elif args.solver == 'yices':
                solver_opts = ["NA", "--mcsat"]

        opt_id = 0
        del cmd_tool[-1]
        cmd_ori = cmd_tool

        idt = 0
        counter = hashlib.md5(tmp_file.encode('utf-8')).hexdigest()
        for opt in solver_opts:
            opt_id += 1
            cmd_new = []
            for ori in cmd_ori:
                cmd_new.append(ori)
            if len(solver_opts) > 1 and opt != "NA":
                cmd_new.append(opt)
            name = '/muta_input-' + str(idt) + "_" + str(opt_id) + "_" + str(counter)[0:6] + '_'
            gene = None
            if args.solvermode == 'sygus':
                gene = StringMutation(tmp_file)
            else:
                gene = StringMutation(tmp_file)
            if args.solvermode == 'unsat_core':
                gene.enable_unsat_core()
            if args.solvermode == 'proof':
                gene.enable_proof()
            if args.solvermode == 'smtopt':
                gene.enable_smtopt()
            if args.optfuzz == 'yes':
                if args.solver == "cvc5":
                    gene.enable_cvc4_option()
                elif args.solver == "z3":
                    gene.enable_z3_option()

            xxxname = name
            for i in range(args.count):
                tmp_file_mut = inputs + name + str(i) + ".smt2"
                xxxname = name + str(i) + ".smt2"
                if args.solvermode == "sygus":
                    tmp_file_mut = inputs + name + str(i) + ".sy"  # or .sl?
                try:
                    with open(tmp_file_mut, 'w') as mut:
                        if args.solvermode == 'exp' and m_has_z3py:  # experimental
                            if not try_z3_mutate(tmp_file, tmp_file_mut):
                                if os.path.isfile(tmp_file_mut):
                                    os.remove(tmp_file_mut)
                                break
                        else:
                            if gene.generate(tmp_file_mut):
                                logging.debug("mutate success")
                            else:
                                if os.path.isfile(tmp_file_mut):
                                    os.remove(tmp_file_mut)
                                break

                except Exception as file_e:
                    print(file_e)
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)
                    continue

                # cmd_mut = cmd_new
                if g_statistic:
                    g_statistic.mutants += 1
                    g_statistic.printbar()
                cmd_mut = []
                for newori in cmd_new:
                    cmd_mut.append(newori)
                cmd_mut.append(tmp_file_mut)
                # print("cmd mut ", cmd_mut)
                logging.debug(cmd_mut)
                pmut = subprocess.Popen(cmd_mut, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
                is_timeout = [False]
                timermut = Timer(5, terminate, args=[pmut, is_timeout])
                timermut.start()

                out_mut = pmut.stdout.readlines()
                out_mut = ' '.join([str(element.decode('UTF-8')) for element in out_mut])
                logging.debug("Mut res: ")
                logging.debug(out_mut)
                # TODO: invalid model message also contains 'error
                bl_msg = ['unsupported', 'what', 'Warning', 'suppress', 'unknown', 'support', 'type', 'Unes']
                if "Santi" in out_mut or 'ASSERTION' in out_mut or 'Assert' in out_mut or 'Fat' in out_mut or (
                        m_test_invalid_model and 'invalid mo' in out_mut):
                    err_flag = True
                    for item in black_list:
                        if not item:
                            continue  # in case there is empty line!
                        if item in out_mut:
                            err_flag = False
                            break
                    if "Santi" not in out_mut:  # crash on error should not be blocked?
                        for blm in bl_msg:
                            if blm in out_mut:
                                err_flag = False
                                break

                    if err_flag:
                        if g_statistic:
                            g_statistic.error += 1
                        print("find error!")
                        print("mut cmd: ", cmd_mut)
                        print("mut res: ", out_mut)
                        print("mut: ", crashes + xxxname)
                        # shutil.copy(tmp_file_mut, outdir + "/crash")
                        shutil.copy(tmp_file_mut, crashes + xxxname)
                        break  # one is enough! ??
                else:
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)
                pmut.stdout.close()
                timermut.cancel()
    except Exception as ee:
        print(ee)


def worker_diff(pack):
    solver = pack[0]  # useless
    tmp_file = pack[1]
    outdir = pack[2]  #

    cmd_tool = []
    if os.stat(tmp_file).st_size == 0:
        print("tmp file empty")
        return
    idt = 0
    counter = hashlib.md5(tmp_file.encode('utf-8')).hexdigest()
    name = '/muta_input-' + str(idt) + "_" + str(counter)[0:6] + '_'

    # Type aware mutation
    gene = StringMutation(tmp_file)

    if args.solvermode == 'unsat_core':
        gene.enable_unsat_core()
    if args.solvermode == 'proof':
        gene.enable_proof()
    if args.solvermode == 'smtopt':
        gene.enable_smtopt()

    if g_statistic:
        g_statistic.seeds += 1

    for i in range(args.count):

        tmp_file_mut = inputs + name + str(i) + ".smt2"
        if args.solvermode == "sygus":
            tmp_file_mut = inputs + name + str(i) + ".sy"  # or .sl?
        try:
            with open(tmp_file_mut, 'w') as mut:
                if args.solvermode == 'exp' and m_has_z3py:  # experimental
                    if not try_z3_mutate(tmp_file, tmp_file_mut):
                        if os.path.isfile(tmp_file_mut):
                            os.remove(tmp_file_mut)
                        break
                else:
                    if gene.generate(tmp_file_mut):
                        logging.debug("mutate success")
                    else:
                        if os.path.isfile(tmp_file_mut):
                            os.remove(tmp_file_mut)
                        break
        except Exception as file_e:
            # print(file_e)
            if os.path.isfile(tmp_file_mut): os.remove(tmp_file_mut)
            continue

        if g_statistic:
            g_statistic.mutants += 1
            g_statistic.printbar()

        with open('test_config.json', 'r') as file:
            config = json.load(file)

        def get_solver_path(solver: str):
            return config.get(solver, solver)

        # Start solving
        m_tools = [
            get_solver_path("z3"),
            get_solver_path("z3") + " rewriter.flat=false",
            get_solver_path("z3") + " smt.arith.solver=2",
            get_solver_path("cvc5")
        ]
        # allow the users to specify the solvers in cmds!
        if args.solvers != "no":
            m_tools = args.solvers.split(";")

        try:
            m_res = []
            for tool in m_tools:
                m_res.append('unknown')
            m_res_out = []
            m_res_tout = []

            for tool in m_tools:
                cmd_tool = []
                for cc in tool.split(' '):
                    cmd_tool.append(cc)

                if 'cvc' in tool:
                    cmd_tool.append('--quiet')
                if 'yice' in tool or 'cvc' in tool or 'boolec' in tool:
                    cmd_tool.append('--incremental')
                env = os.environ.copy()
                env["ASAN_OPTIONS"] = "log_path=stdout:" + \
                                      env.get("ASAN_OPTIONS", "")
                env["ASAN_OPTIONS"] += "detect_leaks=0"

                cmd_tool.append(tmp_file_mut)
                logging.debug(cmd_tool)
                logging.debug(tool)
                ptool = subprocess.Popen(cmd_tool, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
                is_timeout = [False]
                timertool = Timer(10, terminate, args=[ptool, is_timeout])
                timertool.start()
                out_tool = ptool.stdout.readlines()
                out_tool = ' '.join([str(element.decode('UTF-8')) for element in out_tool])
                # logging.debug(out_tool)

                if not is_timeout[0]:  # do not add timeout case
                    m_res_tout.append(False)
                    logging.debug(out_tool)
                    # TODO: keep unknown for finding performance issues
                    bl_msg = ['non-diff', 'unsupported', 'Warning', 'suppress', 'unknown', 'ASSERTION', 'Ass',
                              'ignoring uns', 'not supported', 'Exception', 'Sant', 'Fat', 'inv']
                    bl_msg += ['not defined', 'terminate', 'error', 'suffer', 'Segment', 'Error', 'Invalid',
                               'Unexpected']
                    toadd = True
                    for bl in bl_msg:
                        if bl in out_tool:
                            # if bl == 'Ass' or bl == 'Segment' or bl == 'Fat' or bl == 'Unespected' or bl == 'suffer' or bl == 'terminate':
                            # print("find error")
                            # TODO: record and report error
                            #   shutil.copy(tmp_file_mut, outdir + "/crash")
                            toadd = False
                            break
                    if toadd:
                        m_res_out.append(out_tool)
                else:
                    if not (
                            'true' in out_tool or 'false' in out_tool or 'error' in out_tool or 'an inv' in out_tool or 'Ass' in out_tool or 'ASSERTION' in out_tool):
                        m_res_tout.append(True)
                # close?
                ptool.stdout.close()
                timertool.cancel()

            logging.debug("solving results: ")
            # decide if the elements of the list are equal (solving results are identical)
            # '(' for prunning get value,get model
            if 2 <= len(m_res_out) != m_res_out.count(m_res_out[0]) and '(' not in m_res_out[0]:
                # print("XXX")
                # print(m_res_out[0])
                # print(m_res_out[1])
                print("find inconsistency!")
                # TODO: print the info. of the solvers
                print(tmp_file_mut)
                shutil.copyfile(tmp_file, crashes + name)
                break  # NOTE: one instance is enough
            elif args.perf == "yes" and m_res_tout.count(True) == 1:
                print("find timeout!")
                print(tmp_file_mut)
                break  #
            else:
                if os.path.isfile(tmp_file_mut): os.remove(tmp_file_mut)
        except Exception as ee:
            print(ee)


pool = ThreadPool(processes=args.workers)


def signal_handler(sig, frame):
    pool.terminate()
    if g_statistic:
        g_statistic.printsum()
        if len(g_statistic.profile_data) > 0:
            print("Min: ", min(g_statistic.profile_data))
            print("Max: ", max(g_statistic.profile_data))
            print("Avg: ", sum(g_statistic.profile_data) / len(g_statistic.profile_data))
            print("Std: ", st.pstdev(g_statistic.profile_data))
    os.system('pkill -9 python3')
    os.system('pkill -9 python3.7')
    os.system('pkill -9 python3.8')
    os.system('pkill -9 z3')
    os.system('pkill -9 cvc5')
    os.system('pkill -9 yices_smt2')
    os.system('pkill -9 opensmt')
    os.system('pkill -9 boolector')
    print("We finish here, have a good day!")
    sys.exit(0)


# signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)
signal.signal(signal.SIGQUIT, signal_handler)
signal.signal(signal.SIGHUP, signal_handler)

if args.seed != 'no':
    tasks = []
    seed_files = glob.glob(args.seed + '/**/*.smt2', recursive=True)
    random.shuffle(seed_files)
    if args.logicmode == 'sygus':
        tasks = [(args.solver, f, args.output) for f in seed_files]
    else:
        tasks = [(args.solver, f, args.output) for f in seed_files]

    if args.profile:
        for _ in tqdm.tqdm(pool.imap_unordered(profile, tasks), total=len(tasks)):
            pass
    elif args.diff == 'yes':
        for _ in tqdm.tqdm(pool.imap_unordered(worker_diff, tasks), total=len(tasks)):
            pass
    else:
        for _ in tqdm.tqdm(pool.imap_unordered(worker, tasks), total=len(tasks)):
            pass
    pool.close()
    pool.join()
    print("We finish here, have a good day!")
    if g_statistic:
        g_statistic.printsum()
        if len(g_statistic.profile_data) > 0:
            print("Min: ", min(g_statistic.profile_data))
            print("Max: ", max(g_statistic.profile_data))
            print("Avg: ", sum(g_statistic.profile_data) / len(g_statistic.profile_data))
            print("Std: ", st.pstdev(g_statistic.profile_data))
    sys.exit(0)
else:
    print("Please specify the seed path!")
    pool.close()
    pool.join()
    sys.exit(0)
