# codig: utf-8
import argparse
import configparser
# import itertools
import hashlib
import inspect
import json
import logging
import os
import random
import shutil
import signal
import subprocess
import sys
from multiprocessing.pool import Pool
from threading import Timer

from smtfuzz.mutators.op_mutator import StringMutation

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
parentdir = os.path.dirname(currentdir)

m_bet_mutator = currentdir + '/mutators/bet_mutator.py'

m_has_z3py = True
try:
    from smtfuzz.mutators.bet_mutator import Z3Mutation
except Exception as e:
    print("No z3py, will use StrMut or TyMut")
    m_has_z3py = False

strategies = ['noinc', 'noinc', 'CNFexp', 'cnf', 'ncnf', 'bool', 'bool']

fuzzsmt_logics = ['QF_LRA', 'QF_AUFLIA', 'QF_AX', 'QF_BV', 'QF_IDL', 'QF_LIA',
                  'QF_NIA', 'QF_NRA', 'QF_UF', 'QF_UFBV', 'QF_UFIDL', 'QF_UFLIA', 'QF_UFLRA',
                  'QF_UFNRA', 'QF_UFRDL', 'AUFLIA', 'AUFLIRA', 'AUFNIRA']

# QF_S
qf_int_logic_options = ['QF_IDL', 'QF_NIA', 'QF_LIA', 'QF_ANIA', 'QF_ALIA', 'QF_AUFNIA', 'QF_AUFLIA', 'QF_UFNIA',
                        'QF_UFLIA']
q_int_logic_options = ['ALIA', 'ANIA', 'LIA', 'NIA', 'UFLIA', 'UFNIA', 'AUFLIA', 'AUFNIA']
int_logic_options = qf_int_logic_options + q_int_logic_options

# 'QF_FPLRA', QF_RDL
qf_real_logic_options = ['QF_RDL', 'QF_UFLRA', 'QF_NRA', 'QF_LRA', 'QF_UFNRA', 'QF_AUFNRA', 'QF_AUFLRA']
q_real_logic_options = ['LRA', 'NRA', 'UFLRA', 'UFNRA', 'AUFLRA', 'AUFNRA']
# ANRA, ALRA??
real_logic_options = qf_real_logic_options + q_real_logic_options

qf_bv_logic_options = ['QF_BV', 'QF_UFBV', 'QF_ABV', 'QF_AUFBV']
q_bv_logic_options = ['BV', 'UFBV', 'ABV', 'AUFBV']
bv_logic_options = qf_bv_logic_options + q_bv_logic_options

qf_logic_options = qf_int_logic_options + qf_real_logic_options + qf_bv_logic_options
qf_logic_options.append('BOOL')
q_logic_options = q_int_logic_options + q_real_logic_options + q_bv_logic_options
q_logic_options.append('QBF')

bool_logic_options = ['QF_BOOL', 'QBF', 'QF_UF', 'UF']
# FPLRA
other_logic_options = ['BVINT', 'QF_AX', 'SET', 'QF_FP', 'QF_FPLRA', 'FP', 'FPLRA', 'QF_S', 'QF_SLIA', 'QF_SNIA', 'ALL']

uf_logic_options = ['QF_UF', 'QF_UFLIA', 'QF_UFLRA', 'QF_UFNRA', 'QF_UFNIA', 'QF_AUFLIA', 'QF_AUFLRA', 'QF_AUFNIA',
                    'QF_AUFNRA', 'QF_UFC', 'QF_UFLIRA', 'QF_UFNIRA', 'QF_AUFLIRA', 'QF_AUFNIRA']
uf_logic_options += ['UF', 'UFLIA', 'UFLRA', 'UFNRA', 'UFNIA', 'AUFLIA', 'AUFLRA', 'AUFNIA', 'AUFNRA', 'UFC', 'UFLIRA',
                     'UFNIRA', 'AUFLIRA', 'AUFNIRA']

lira_logics = ['QF_LIRA', 'LIRA', 'QF_ALIRA', 'ALIRA', 'QF_UFLIRA', 'UFLIRA', 'QF_AUFLIRA', 'AUFLIRA']
nira_logics = ['QF_NIRA', 'NIRA', 'QF_ANIRA', 'ANIRA', 'QF_UFNIRA', 'UFNIRA', 'QF_AUFNIRA', 'AUFNIRA']
ira_logics = lira_logics + nira_logics

# linear
# QF_RDL, QF_IDL
qfla_logics = ['QF_LIRA', 'QF_ALIRA', 'QF_UFLIRA', 'QF_LIA', 'QF_ALIA', 'QF_AUFLIA', 'QF_UFLIA', 'QF_UFLRA', 'QF_LRA',
               'QF_AUFLR']
qla_logics = ['ALIA', 'LIA', 'UFLIA', 'AUFLIA', 'LRA', 'UFLRA', 'AUFLRA', 'LIRA', 'UFLIRA', 'AUFLIRA']
la_logics = qfla_logics + qla_logics

all_logic_options = []
all_logic_options += qf_logic_options
all_logic_options += q_logic_options
all_logic_options += bool_logic_options
all_logic_options += other_logic_options
all_logic_options += ira_logics

logics = all_logic_options

weight_strategy = [1] * len(strategies)
weight_logic = [1] * len(logics)
cnfratio = random.randint(1, 30)
cntsize = random.randint(2, 200)

# m_num_process = multiprocessing.cpu_count()

parser = argparse.ArgumentParser()
parser.add_argument('--input', dest='input', type=str)
parser.add_argument('--output', dest='output', default='~/tmp/res/', type=str)
parser.add_argument('--timeout', dest='timeout', default=10, type=int, help="timeout for each solving")
parser.add_argument('--count', dest='count', default=50, type=int, help="counts for each combination")
parser.add_argument('--workers', dest='workers', default=1, type=int, help="num threads")

parser.add_argument('--solvermode', dest='solvermode', default='default', type=str)
parser.add_argument('--logicmode', dest='logicmode', default='default', type=str)
parser.add_argument('--optfuzz', dest='optfuzz', default='no', type=str)

parser.add_argument('--config', dest='config', default='no', type=str)
parser.add_argument('--solver', dest='solver', default='all', type=str)

parser.add_argument("-v", "--verbose", help="increase output verbosity",
                    action="store_true")

args = parser.parse_args()

if args.verbose:
    logging.basicConfig(level=logging.DEBUG)

m_num_process = args.workers  # thread

black_list = []
black_list_files = ['../black_list_cvc4_new', '../black_list_z3', '../black_list_open', '../black_list_yices2']
for f in black_list_files:
    bf = open(f, 'r')
    for line in bf:
        black_list.append(line.replace("\n", ""))
    bf.close()

    # Load the configuration file


with open('test_config.json', 'r') as file:
    m_config = json.load(file)


def get_smt_solver_path(solver: str):
    return m_config.get(solver, solver)


m_tools = [
    get_smt_solver_path("z3"),
    get_smt_solver_path("cvc5")
]

generator = 'generator.py'

if args.config != 'no':
    m_config = configparser.ConfigParser()
    m_config.read(args.config)
    print(list(m_config['DIFFSOLVERS'].values()))
    m_tools = list(m_config['DIFFSOLVERS'].values())

in_dir = args.input
out_dir = args.output
timeout = args.timeout
count = args.count

m_solver_mode = args.solvermode
m_logic_mode = args.logicmode  # TODO: set logic mode. e.g. only test a group of logics of a certain one

m_test_maxsmt = False
if m_solver_mode == "maxsmt":
    m_test_maxsmt = True

shutil.rmtree(out_dir)
os.mkdir(out_dir)

crashes = out_dir + '/crash'
inputs = out_dir + '/input'
os.mkdir(crashes)
os.mkdir(inputs)


def find_smt2(path):
    flist = []  # path to smtlib2 files
    for root, dirs, files in os.walk(path):
        for fname in files:
            if os.path.splitext(fname)[1] == '.smt2':
                flist.append(os.path.join(root, fname))
    return flist


def rand_partition(list_in, n):
    random.shuffle(list_in)
    return [list_in[ii::n] for ii in range(n)]


def split_list(alist, wanted_parts=1):
    length = len(alist)
    return [alist[i * length // wanted_parts: (i + 1) * length // wanted_parts]
            for i in range(wanted_parts)]


def terminate(process, is_timeout):
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as e:
            print("error for interrupting")
            print(e)


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
    timer = Timer(10, terminate, args=[p, is_timeout])
    timer.start()
    out = p.stdout.readlines()
    out = ' '.join([str(element.decode('UTF-8')) for element in out])
    # print(out)
    if is_timeout[0]:  # do not add timeout case
        logging.debug("Timeout when using z3py for mutation")
        ret = False
    elif "error" in out or "Segment" in out or "Exception" in out:
        logging.debug("Error when usng z3py for mutation!")
        ret = False

    p.stdout.close()
    timer.cancel()
    return ret


def gen_and_mut(idt):
    global generator
    counter = 0
    while True:
        try:
            if counter % count == 0 and (
                    m_solver_mode == "default" or m_solver_mode == "exp" or m_solver_mode == "proof"
                    or m_solver_mode == "interpolant" or m_solver_mode == "unsat_core"):
                logging.debug("enter parameter generations")
                cnfratio = random.randint(2, 50)
                cntsize = random.randint(25, 550)
                strategy = random.randint(0, len(strategies) - 1)
                if m_solver_mode == "exp":
                    strategy = 0
                logic = random.randint(0, len(logics) - 1)
                logiclist = logics
                if m_logic_mode == 'bv':
                    logiclist = bv_logic_options
                elif m_logic_mode == 'int':
                    logiclist = int_logic_options
                elif m_logic_mode == 'real':
                    logiclist = real_logic_options
                elif m_logic_mode == 'bool':
                    logiclist = bool_logic_options
                elif m_logic_mode == 'str':
                    logiclist = ['QF_S', 'QF_SLIA', 'QF_SNIA']
                elif m_logic_mode == 'qu':
                    logiclist = q_logic_options
                elif m_logic_mode == 'qf':
                    logiclist = qf_logic_options
                elif m_logic_mode == 'new':
                    logiclist = ira_logics
                elif m_logic_mode == 'uf':
                    logiclist = uf_logic_options
                elif m_logic_mode == 'qfla':
                    logiclist = qfla_logics
                elif m_logic_mode == 'la':
                    logiclist = la_logics
                else:
                    logiclist = qf_logic_options

                logic = random.randint(0, len(logiclist) - 1)
                counter = 0

            elif counter % count == 0 and (
                    m_solver_mode == "smtopt" or m_solver_mode == "maxsmt"):  # can we have quantifier for maxsmt?
                cnfratio = random.randint(2, 25)  # should we do this?
                cntsize = random.randint(3, 120)
                strategy = random.randint(0, len(strategies) - 1)
                logic = random.randint(0, len(qf_logic_options) - 1)
                logiclist = qf_logic_options

                if m_logic_mode == 'bv':
                    logic = random.randint(0, len(qf_bv_logic_options) - 1)
                    logiclist = qf_bv_logic_options
                elif m_logic_mode == 'int':
                    logic = random.randint(0, len(qf_int_logic_options) - 1)
                    logiclist = qf_int_logic_options
                elif m_logic_mode == 'real':
                    logic = random.randint(0, len(qf_real_logic_options) - 1)
                    logiclist = qf_real_logic_options
                counter = 0
            final_logic_to_use = logiclist[logic]

            if m_logic_mode in all_logic_options:  # allow to select a fixed logic
                final_logic_to_use = m_logic_mode

            name = '/diff_input-' + str(idt) + "_" + str(counter) + '_' + strategies[strategy] + '_' + \
                   str(cnfratio) + '_' + str(cntsize) + '_' + str(final_logic_to_use) + '.smt2'
            tmp_file = inputs + name

            counter += 1
            cmd = ['python3', generator, '--strategy', str(strategies[strategy]), '--cnfratio', str(cnfratio),
                   '--cntsize', str(cntsize), '--logic', str(final_logic_to_use), '--difftest', '1']

            if m_solver_mode == "unsat_core":  # special for difftest
                cmd.append('--difftestcore')
                cmd.append('1')

            elif m_solver_mode == "proof":
                cmd.append('--proof')
                cmd.append('1')

            logging.debug("Enter constraint generation")
            logging.debug(cmd)
            p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            is_timeout_gene = [False]
            timer_gene = Timer(15, terminate, args=[p_gene, is_timeout_gene])
            timer_gene.start()
            out_gene = p_gene.stdout.readlines()
            out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
            f = open(tmp_file, 'w')
            f.write(out_gene)
            f.close()
            p_gene.stdout.close()  # close?
            timer_gene.cancel()

            if os.stat(tmp_file).st_size == 0:
                print("seed file empty")
                continue

            # Starting to mutate
            cmd_tool = []
            to_test = None
            if args.solver == 'yices':
                to_test = get_smt_solver_path("yices")
            elif args.solver == 'cvc5':
                to_test = get_smt_solver_path("cvc5")
            elif args.solver == 'z3':
                to_test = get_smt_solver_path("z3")
            elif args.solver == 'open':
                to_test = get_smt_solver_path("open")
            elif args.solver == 'pol':
                to_test = get_smt_solver_path("pol")
            else:
                to_test = get_smt_solver_path("z3")

            for cc in to_test.split(' '):  # currently, choose the first tool
                cmd_tool.append(cc)

            # TODO: always --incremental is not good
            if 'cvc' in to_test:
                cmd_tool.append('--quiet')
                # if random.random() < 0.3:
                if str(final_logic_to_use) in ['QF_S', 'SEQ', 'QF_SLIA', 'QF_SNIA', 'QF_UFSLIA']:
                    cmd_tool.append('--strings-exp')
                elif str(final_logic_to_use) == 'SET':
                    cmd_tool.append('--sets-ext')
                if str(strategies[strategy]) != 'noinc':
                    cmd_tool.append('--incremental')
                cmd_tool.append('--check-models')

            if 'yice' in to_test or 'boolec' in to_test:
                if str(strategies[strategy]) != 'noinc':
                    cmd_tool.append('--incremental')

            logging.debug("Enter seed solving")
            cmd_seed = cmd_tool
            cmd_seed.append(tmp_file)
            logging.debug("Seed res: ")
            logging.debug(cmd_seed)
            env = os.environ.copy()
            env["ASAN_OPTIONS"] = "log_path=stdout:" + \
                                  env.get("ASAN_OPTIONS", "")
            env["ASAN_OPTIONS"] += "detect_leaks=0"
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
                if os.path.isfile(tmp_file):
                    os.remove(tmp_file)
                continue

            elif "unknown logic" in out_seed or "error" in out_seed:
                ptool.stdout.close()
                timertool.cancel()
                if os.path.isfile(tmp_file):
                    os.remove(tmp_file)
                continue

            ptool.stdout.close()
            timertool.cancel()

            logging.debug("Enter mutation and solving")

            tmp_file_md5 = str(hashlib.md5(tmp_file.encode('utf-8')).hexdigest())
            name = '/muta_input-' + str(idt) + "_" + tmp_file_md5[0:6]
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

            for i in range(args.count):
                tmp_file_mut = inputs + name + "_" + str(i) + ".smt2"
                try:
                    with open(tmp_file_mut, 'w') as mut:
                        if args.solvermode == 'exp' and m_has_z3py:  # experimental
                            if not try_z3_mutate(tmp_file, tmp_file_mut):
                                if os.path.isfile(tmp_file_mut):
                                    os.remove(tmp_file_mut)
                                # use the original mutant
                                if gene.generate(tmp_file_mut):
                                    logging.debug("mutate success")
                                else:
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
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)

                del cmd_tool[-1]
                cmd_mut = cmd_tool
                cmd_mut.append(tmp_file_mut)
                logging.debug(cmd_mut)
                pmut = subprocess.Popen(cmd_mut, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
                is_timeout = [False]
                timermut = Timer(10, terminate, args=[pmut, is_timeout])
                timermut.start()

                out_mut = pmut.stdout.readlines()
                out_mut = ' '.join([str(element.decode('UTF-8')) for element in out_mut])
                logging.debug("Mut res: ")
                logging.debug(out_mut)
                # TODO: invalid model message also contains 'error
                bl_msg = ['unsupported', 'what', 'Warning', 'suppress', 'unknown', 'support', 'type', 'Unes']

                if "Santi" in out_mut or 'ASS' in out_mut or 'Ass' in out_mut \
                        or 'Fat' in out_mut or 'invalid mo' in out_mut:
                    err_flag = True
                    for item in black_list:
                        if not item:
                            continue  # in case there is empty line!
                        if item in out_mut:
                            err_flag = False
                            break

                    for blm in bl_msg:
                        if blm in out_mut:
                            err_flag = False
                            break

                    if err_flag:
                        print("find error!")
                        print("mut res: ", out_mut)
                        print("mut: ", tmp_file_mut)
                        shutil.copy(tmp_file_mut, out_dir + "/crash")
                else:
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)
                pmut.stdout.close()
                timermut.cancel()

            if os.path.isfile(tmp_file):
                os.remove(tmp_file)
        except Exception as e:
            # remove file?
            if 'timed out' not in e:
                print(e)


# metamorphic, currently only mutate options
def gen_and_meta(idt):
    global generator
    counter = 0
    while True:
        try:
            if counter % count == 0 and (
                    m_solver_mode == "default" or m_solver_mode == "exp" or
                    m_solver_mode == "proof" or m_solver_mode == "interpolant" or
                    m_solver_mode == "unsat_core"):
                logging.debug("enter parameter generations")
                cnfratio = random.randint(2, 50)
                cntsize = random.randint(25, 550)
                strategy = random.randint(0, len(strategies) - 1)
                if m_solver_mode == "exp":
                    strategy = 0
                logic = random.randint(0, len(logics) - 1)
                logiclist = logics
                if m_logic_mode == 'bv':
                    logiclist = bv_logic_options
                elif m_logic_mode == 'int':
                    logiclist = int_logic_options
                elif m_logic_mode == 'real':
                    logiclist = real_logic_options
                elif m_logic_mode == 'bool':
                    logiclist = bool_logic_options
                elif m_logic_mode == 'str':
                    logiclist = ['QF_S', 'QF_SLIA', 'QF_SNIA']
                elif m_logic_mode == 'qu':
                    logiclist = q_logic_options
                elif m_logic_mode == 'qf':
                    logiclist = qf_logic_options
                elif m_logic_mode == 'new':
                    logiclist = ira_logics
                elif m_logic_mode == 'uf':
                    logiclist = uf_logic_options
                elif m_logic_mode == 'qfla':
                    logiclist = qfla_logics
                elif m_logic_mode == 'la':
                    logiclist = la_logics
                else:
                    logiclist = qf_logic_options

                logic = random.randint(0, len(logiclist) - 1)
                counter = 0

            final_logic_to_use = logiclist[logic]

            if m_logic_mode in all_logic_options:  # allow to select a fixed logic
                final_logic_to_use = m_logic_mode

            name = '/diff_input-' + str(idt) + "_" + str(counter) + '_' + strategies[strategy] + '_' + \
                   str(cnfratio) + '_' + str(cntsize) + '_' + str(final_logic_to_use) + '.smt2'
            tmp_file = inputs + name

            counter += 1
            cmd = ['python3', generator, '--strategy', str(strategies[strategy]), '--cnfratio', str(cnfratio),
                   '--cntsize', str(cntsize), '--logic', str(final_logic_to_use), '--difftest', '1']

            if m_solver_mode == "unsat_core":  # special for difftest
                cmd.append('--difftestcore')
                cmd.append('1')

            elif m_solver_mode == "interpolant":
                cmd.append('--interpolant')
                cmd.append('1')

            elif m_solver_mode == "proof":
                cmd.append('--proof')
                cmd.append('1')

            logging.debug("Enter constraint generation")
            logging.debug(cmd)
            p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            is_timeout_gene = [False]
            timer_gene = Timer(15, terminate, args=[p_gene, is_timeout_gene])
            timer_gene.start()
            out_gene = p_gene.stdout.readlines()
            out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
            f = open(tmp_file, 'w')
            f.write(out_gene)
            f.close()
            p_gene.stdout.close()  # close?
            timer_gene.cancel()

            if os.stat(tmp_file).st_size == 0:
                print("seed file empty")
                continue

            # Load the configuration file

            # Starting to mutate
            cmd_tool = []
            to_test = None
            if args.solver == 'cvc5':
                to_test = get_smt_solver_path("cvc5")
            elif args.solver == 'z3':
                to_test = get_smt_solver_path("z3")
            else:
                to_test = get_smt_solver_path("z3")

            for cc in to_test.split(' '):  # currently, choose the first tool
                cmd_tool.append(cc)

            # TODO: always --incremental is not good
            if 'cvc' in to_test:
                cmd_tool.append('--quiet')
                # if random.random() < 0.3:
                if str(final_logic_to_use) in ['QF_S', 'SEQ', 'QF_SLIA', 'QF_SNIA', 'QF_UFSLIA']:
                    cmd_tool.append('--strings-exp')
                elif str(final_logic_to_use) == 'SET':
                    cmd_tool.append('--sets-ext')
                if str(strategies[strategy]) != 'noinc':
                    cmd_tool.append('--incremental')
                cmd_tool.append('--check-models')

            if 'yice' in to_test or 'boolec' in to_test:
                if str(strategies[strategy]) != 'noinc':
                    cmd_tool.append('--incremental')

            logging.debug("Enter seed solving")
            cmd_seed = cmd_tool
            cmd_seed.append(tmp_file)
            logging.debug("Seed res: ")
            logging.debug(cmd_seed)
            env = os.environ.copy()
            env["ASAN_OPTIONS"] = "log_path=stdout:" + \
                                  env.get("ASAN_OPTIONS", "")
            env["ASAN_OPTIONS"] += "detect_leaks=0"
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
                if os.path.isfile(tmp_file):
                    os.remove(tmp_file)
                continue

            elif "unknown logic" in out_seed or "error" in out_seed:
                ptool.stdout.close()
                timertool.cancel()
                if os.path.isfile(tmp_file):
                    os.remove(tmp_file)
                continue

            ptool.stdout.close()
            timertool.cancel()

            logging.debug("Enter mutation and solving")

            tmp_file_md5 = str(hashlib.md5(tmp_file.encode('utf-8')).hexdigest())
            name = '/muta_input-' + str(idt) + "_" + tmp_file_md5[0:6]
            gene = StringMutation(tmp_file)
            gene.pure_option_mode = True

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

            for i in range(args.count):
                tmp_file_mut = inputs + name + "_" + str(i) + ".smt2"
                try:
                    with open(tmp_file_mut, 'w') as mut:
                        if gene.generate(tmp_file_mut):
                            logging.debug("mutate success")
                        else:
                            if os.path.isfile(tmp_file_mut):
                                os.remove(tmp_file_mut)
                            break
                except Exception as file_e:
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)

                del cmd_tool[-1]
                cmd_mut = cmd_tool
                cmd_mut.append(tmp_file_mut)
                logging.debug(cmd_mut)
                pmut = subprocess.Popen(cmd_mut, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
                is_timeout = [False]
                timermut = Timer(10, terminate, args=[pmut, is_timeout])
                timermut.start()

                out_mut = pmut.stdout.readlines()
                out_mut = ' '.join([str(element.decode('UTF-8')) for element in out_mut])
                logging.debug("Mut res: ")
                logging.debug(out_mut)
                # TODO: invalid model message also contains 'error
                bl_msg = ['unsupported', 'error', 'loop', 'what', 'Warning', 'suppress',
                          'unknown', 'support', 'type', 'Unes']

                if not is_timeout[0] and out_seed != out_mut \
                        and os.path.isfile(tmp_file):
                    err_flag = True
                    for item in black_list:
                        if not item:
                            continue  # in case there is empty line!
                        if item in out_mut:
                            err_flag = False
                            break

                    if "kflips" in out_mut:
                        err_flag = True

                    for blm in bl_msg:
                        if blm in out_mut or blm in out_seed:
                            err_flag = False
                            break
                    if err_flag:
                        print("find inconsistency!")
                        print("seed res: ", out_seed)
                        print("mut res: ", out_mut)
                        print("seed: ", tmp_file)
                        print("mut: ", tmp_file_mut)
                        shutil.copy(tmp_file, out_dir + "/crash")
                        shutil.copy(tmp_file_mut, out_dir + "/crash")

                if "Santi" in out_mut or 'ASS' in out_mut or 'Ass' in out_mut or\
                        'Fat' in out_mut or 'invalid mo' in out_mut:
                    err_flag = True
                    for item in black_list:
                        if not item:
                            continue  # in case there is empty line!
                        if item in out_mut:
                            err_flag = False
                            break

                    for blm in bl_msg:
                        if blm in out_mut:
                            err_flag = False
                            break

                    if err_flag:
                        print("find error!")
                        print("mut res: ", out_mut)
                        print("mut: ", tmp_file_mut)
                        shutil.copy(tmp_file_mut, out_dir + "/crash")
                else:
                    if os.path.isfile(tmp_file_mut):
                        os.remove(tmp_file_mut)
                pmut.stdout.close()
                timermut.cancel()

            if os.path.isfile(tmp_file):
                os.remove(tmp_file)
        except Exception as e:
            # remove file?
            if 'timed out' not in e:
                print(e)


tp = Pool(m_num_process)


def signal_handler(sig, frame):
    tp.terminate()
    print("We finish here, have a good day!")
    os.system('pkill -9 python3')
    os.system('pkill -9 python3.7')
    os.system('pkill -9 python3.8')
    os.system('pkill -9 z3')
    os.system('pkill -9 cvc5')
    os.system('pkill -9 yices_smt2')
    os.system('pkill -9 opensmt')
    os.system('pkill -9 boolector')
    sys.exit(0)


# signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)
signal.signal(signal.SIGQUIT, signal_handler)
signal.signal(signal.SIGHUP, signal_handler)

for i in range(0, m_num_process):
    tp.apply_async(gen_and_meta, args=(i,))
tp.close()
tp.join()
print("We finish here, have a good day!")
sys.exit(0)
