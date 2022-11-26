# coding: utf-8
"""
In this example, we will use fuzzlib/generators/smtfuzz.py to generate an SMT formula.
(The result is an SMT-LIB2 string)

"""
import os
from threading import Timer
import subprocess
import random
from os.path import dirname, abspath

parent_dir = dirname(dirname(abspath(__file__)))
if os.name == "nt":  # Windows?
    generator = parent_dir + '\\fuzzlib\generators\smtfuzz.py'
else:
    generator = parent_dir + '/fuzzlib/generators/smtfuzz.py'

strategies = ['noinc', 'noinc', 'CNFexp', 'cnf', 'ncnf', 'bool', 'bool']


def terminate(process, is_timeout):
    """
    Terminate the process and set is_timeout[0] to be true
    @param process:
    @param is_timeout:
    @return:
    """
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as e:
            print("error for interrupting")
            print(e)


def generate_from_grammar_as_str(logic="QF_BV", incremental=False) -> str:
    """Generate an SMT-LIB2 string"""
    cnfratio = random.randint(2, 10)
    cntsize = random.randint(5, 20)
    if incremental:
        strategy = random.choice(['CNFexp', 'cnf', 'ncnf', 'bool'])
    else:
        strategy = 'noinc'

    cmd = ['python3', generator,
           '--strategy', strategy,
           '--cnfratio', str(cnfratio),
           '--cntsize', str(cntsize),
           '--disable', 'option_fuzzing',
           '--difftest', '1',
           '--logic', logic]

    # print(cmd)

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


if __name__ == "__main__":
    # this is for pruning files tha take a long time for parsing?
    print(generate_from_grammar_as_str())