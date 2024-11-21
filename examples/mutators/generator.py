import inspect
import os
import random
import subprocess
from threading import Timer

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
parentdir = os.path.dirname(currentdir)

generator = parentdir + '/smtfuzz/smtfuzz.py'

strategies = ['noinc', 'noinc', 'CNFexp', 'cnf', 'ncnf', 'bool', 'bool']

logiclist = ['LRA', 'NRA', 'QF_LRA', 'QF_NRA', 'QF_UFNRA']
logiclist += ['LIA', 'NIA', 'QF_LIA', 'QF_NIA', 'QF_UFNIA']
logiclist += ['BV', 'ABV', 'QF_BV', 'QF_AUFBV']


# logiclist += ['QF_S', 'QF_SLIA', 'QF_SNIA']
# logiclist += ['QF_FP', 'QF_FPLRA']
# logiclist += ['UFLIRA', 'QF_UFNIRA', 'UFNIRA']

def terminate(process, is_timeout):
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as e:
            print("error for interrupting")
            print(e)


def grammar_mutate(input, output):
    cmd = ['python3', generator, '--outputfile', str(output), input]

    p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    is_timeout_gene = [False]
    timer_gene = Timer(15, terminate, args=[p_gene, is_timeout_gene])
    timer_gene.start()
    # out_gene = p_gene.stdout.readlines()
    # out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
    p_gene.stdout.close()  # close?
    timer_gene.cancel()
    if os.stat(output).st_size == 0 or is_timeout_gene[0]:
        return False
    return True


def generate_from_grammar_as_str():
    cnfratio = random.randint(2, 50)
    cntsize = random.randint(15, 150)

    strategy = random.randint(0, len(strategies) - 1)

    logic = random.randint(0, len(logiclist) - 1)
    final_logic_to_use = logiclist[logic]

    cmd = ['python3', generator, '--strategy', str(strategies[strategy]),
           '--cnfratio', str(cnfratio), '--cntsize',
           str(cntsize), '--logic', str(final_logic_to_use)]

    p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    is_timeout_gene = [False]
    timer_gene = Timer(15, terminate, args=[p_gene, is_timeout_gene])
    timer_gene.start()
    out_gene = p_gene.stdout.readlines()
    out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
    p_gene.stdout.close()  # close?
    timer_gene.cancel()
    if is_timeout_gene[0]:
        return False
    return out_gene


def generate_from_grammar_to_file(output):
    cnfratio = random.randint(2, 50)
    cntsize = random.randint(15, 250)

    strategy = random.randint(0, len(strategies) - 1)

    logic = random.randint(0, len(logiclist) - 1)
    final_logic_to_use = logiclist[logic]

    cmd = ['python3', generator, '--strategy', str(strategies[strategy]),
           '--cnfratio', str(cnfratio), '--cntsize',
           str(cntsize), '--logic', str(final_logic_to_use)]

    p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    is_timeout_gene = [False]
    timer_gene = Timer(15, terminate, args=[p_gene, is_timeout_gene])
    timer_gene.start()
    out_gene = p_gene.stdout.readlines()
    out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
    f = open(output, 'w')
    f.write(out_gene)
    f.close()
    p_gene.stdout.close()  # close?
    timer_gene.cancel()
    if os.stat(output).st_size == 0 or is_timeout_gene[0]:
        # print("error: seed file empty")
        return False
    return True


if __name__ == "__main__":
    # this is for pruning files tha take a long time for parsing?
    generate_from_grammar_to_file("test.smt2")
