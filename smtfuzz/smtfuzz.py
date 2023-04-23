# coding: utf-8
"""
This file generates SMT-LIB2 formulas for fuzz testing SMT solvers.
It includes various options and configurations to control the generation process
"""

import argparse
import itertools
import math
import random
import signal
import string
import sys
from collections import OrderedDict

m_set_logic = True  # generate the (set-logic ...) command

m_strict_cnf = False  # generate formulas in CNF form

m_reset_assert = False  # generate the (reset-assertions) and (reset) commands
m_reset_cmd = '(reset-assertions)'
if random.random() < 0.2:
    m_reset_cmd = '(reset)'

m_test_fp64 = False  # default Float32
if random.random() < 0.5:
    m_test_fp64 = True
m_fp_rounding_mode = "random"  # rounding mode for FP
if random.random() < 0.8:  # use fixed?
    fp_round_pp = random.random()
    if fp_round_pp < 0.2:
        m_fp_rounding_mode = "RNE"
    elif fp_round_pp < 0.4:
        m_fp_rounding_mode = "RNA"
    elif fp_round_pp < 0.6:
        m_fp_rounding_mode = "RTP"
    elif fp_round_pp < 0.8:
        m_fp_rounding_mode = "RTN"
    else:
        m_fp_rounding_mode = "RTZ"

m_test_iand = False  # test the iand feature
m_test_eqrange = False  # test eqrange

# Swarm testing
m_quantifier_rate_swarm = [0.11, 0.22, 0.33, 0.44, 0.55, 0.66]
m_or_and_rate_swarm = [0.11, 0.22, 0.33, 0.44, 0.55, 0.66]
m_exists_forall_rate_swarm = [0.11, 0.22, 0.33, 0.44, 0.55, 0.66]
m_assert_or_create_new_swarm = [0.11, 0.22, 0.33, 0.44, 0.55, 0.66]
m_create_exp_rate_swarm = [0.11, 0.22, 0.33, 0.44, 0.55, 0.66]
m_create_bool_rate_swarm = [0.11, 0.22, 0.33, 0.44, 0.55, 0.66]
m_push_pop_rate_swarm = [0.05, 0.1, 0.15, 0.2, 0.25]

m_declare_new_var_swarm = [0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.40]

m_max_smt_rate = random.uniform(1.05, 1.66) - 1

m_quantifier_rate = random.choice(m_quantifier_rate_swarm)
m_or_and_rate = random.choice(m_or_and_rate_swarm)
m_exists_forall_rate = random.choice(m_exists_forall_rate_swarm)
m_assert_or_create_new = random.choice(m_assert_or_create_new_swarm)
m_create_exp_rate = random.choice(m_create_exp_rate_swarm)
m_create_bool_rate = random.choice(m_create_bool_rate_swarm)
m_push_pop_rate = random.choice(m_push_pop_rate_swarm)
m_declare_new_var_rate = random.choice(m_declare_new_var_swarm)

# default 20 (the number of vars to crate at the beginning)
m_init_var_size = 20

m_use_swarm_bv = False  # selectively reduce the number of bv-operations
# if random.random() < 0.5: m_use_swarm_bv = True
m_use_bv_concat_repeat = True
# if random.random() < 0.33: m_use_bv_concat_repeat = False

m_use_swarm_fp = False  # selectively reduce the number of fp-operations
if random.random() < 0.33:
    m_use_swarm_fp = True

m_use_fancy_qterm = False  # create fancy quantified assertions
if random.random() < 0.66:
    m_use_fancy_qterm = True

m_use_ite = False  # ite(b s1 s2)
if random.random() < 0.22:
    m_use_ite = True

# Advanced features
m_test_smt_opt = False  # (maximize x)
m_test_smt_opt_fancy_term = False
if random.random() < 0.33:
    m_test_smt_opt_fancy_term = True

m_test_max_smt = False  # test MaxSMT, e.g., (assert-soft xx)
m_test_qe = False  # test quantifier elimination
m_test_unsat_core = False  # test unsat core
m_test_interpolant = False  # test interpolant

# The following items are used for maintaining the scope information
# when using push/pop commands
m_assert_id = 0  # id for naming assertions in unsat_core
m_all_assertions = []
m_backtrack_points = []
n_push = 0
n_pop = 0
m_fancy_push = False
# if random.random() < 0.25: m_fancy_push = True

m_test_proof = False  # test proof generation

m_test_named_assert = False  # test named assertions

m_test_pure_sat = False  # SAT
m_test_qbf = False  # QBF
m_test_max_sat = False  # maxsatm_test_allsat

m_test_set_bapa = False  # Set and/or BAPA
m_test_str_set_bapa = False  # Set of strings
m_test_bag_bapa = False  # Bag and/or BAPA
m_test_set_comprehension = False
m_test_set_eq = False  # seteq

# String-related o
m_test_string = False  # Test string
m_test_string_lia = False
m_test_seq = False

m_test_string_substr = False
if random.random() < 0.33:
    m_test_string_substr = True

m_test_string_re = False
if random.random() < 0.5:
    m_test_string_re = True  # TODO: many re operations are not added

m_test_string_replace = False
if random.random() < 0.33:
    m_test_string_replace = True

m_test_string_unicode = False
if random.random() < 0.22:
    m_test_string_unicode = True

m_use_swarm_str = False  # selectively reduce the number of str-operations
if random.random() < 0.5:
    m_use_swarm_str = True

"""
FP related
"""
m_test_fp = False  # Test FP
m_test_fp_no_num = False  # FP, but do not create any num.
m_test_fp_lra = False

m_test_seplog = False  # Separation logic

"""Datalog/CHC"""
m_test_datalog_chc = False  # Datalog and CHC
m_test_datalog_chc_logic = "int"  # underlying theory
m_test_datalog_chc_var_bound = 3  # max. number of variable in each rule
m_test_datalog_chc_nonlinear = False  # generate non-linear term of not
m_test_datalog_chc_as_tactic = False  # test CHC with "horn" tactic

"""Recursive function"""
m_test_recfun = False  # recursive function
m_test_recfun_logic = "int"

m_test_my_uf = False  # uninterpreted functions

m_test_bvint = False  # BV and INT

m_noinc_mode = False

m_test_ufc = False  # UF with card

# eldarica
m_test_eldarica = False

# diff
m_test_diff = False
m_test_diff_core = False

# Global info.
m_global_logic = ''
m_global_strategy = ''

# option fuzz mode
m_optionmode = 'full'  # none, basic, full

# should be QF_SLIA?
# QF_IDL, IDL
qf_int_logic_options = [
    'QF_UFIDL',
    'QF_IDL',
    'QF_S',
    'QF_SLIA',
    'QF_UFSLIA',
    'QF_SNIA',
    'QF_NIA',
    'QF_LIA',
    'QF_ANIA',
    'QF_ALIA',
    'QF_AUFNIA',
    'QF_AUFLIA',
    'QF_UFNIA',
    'QF_UFLIA']
q_int_logic_options = [
    'ALIA',
    'ANIA',
    'LIA',
    'NIA',
    'UFLIA',
    'UFNIA',
    'AUFLIA',
    'AUFNIA']
int_logic_options = qf_int_logic_options + q_int_logic_options

# QF_RDL, RDL
qf_real_logic_options = [
    'QF_UFRDL',
    'QF_RDL',
    'QF_ANRA',
    'QF_ALRA',
    'QF_FPLRA',
    'QF_UFLRA',
    'QF_NRA',
    'QF_LRA',
    'QF_UFNRA',
    'QF_AUFNRA',
    'QF_AUFLRA']
q_real_logic_options = [
    'ANRA',
    'ALRA',
    'LRA',
    'NRA',
    'UFLRA',
    'UFNRA',
    'AUFLRA',
    'AUFNRA']

lira_logics = [
    'QF_LIRA',
    'QF_SLIRA',
    'LIRA',
    'QF_ALIRA',
    'ALIRA',
    'QF_UFLIRA',
    'UFLIRA',
    'QF_AUFLIRA',
    'AUFLIRA']
nira_logics = [
    'QF_NIRA',
    'NIRA',
    'QF_ANIRA',
    'ANIRA',
    'QF_UFNIRA',
    'UFNIRA',
    'QF_AUFNIRA',
    'AUFNIRA']
qf_ira_logics = [
    'QF_LIRA',
    'QF_SLIRA',
    'QF_ALIRA',
    'QF_UFLIRA',
    'QF_AUFLIRA',
    'QF_NIRA',
    'QF_ANIRA',
    'QF_UFNIRA',
    'QF_AUFNIRA']

# QF_SNIA is not included
lia_logics = [
    'QF_SLIA',
    'SEQ',
    'QF_UFSLIA',
    'QF_UFSLIA',
    'IDL',
    'QF_IDL',
    'QF_UFIDL',
    'LIA',
    'UFLIA',
    'ALIA',
    'AUFLIA',
    'QF_LIA',
    'QF_UFLIA',
    'QF_ALIA',
    'QF_AUFLIA']
lra_logics = [
    'QF_RDL',
    'QF_UFRDL',
    'RDL',
    'QF_FPLRA',
    'FPLRA',
    'LRA',
    'QF_LRA',
    'UFLRA',
    'QF_UFLRA',
    'AUFLRA',
    'QF_AUFLRA']

lia_logics += lira_logics
lra_logics += lira_logics

# ANRA, ALRA??
real_logic_options = qf_real_logic_options + q_real_logic_options

qf_bv_logic_options = ['QF_BV', 'QF_UFBV', 'QF_ABV', 'QF_AUFBV']
q_bv_logic_options = ['BV', 'UFBV', 'ABV', 'AUFBV']
bv_logic_options = qf_bv_logic_options + q_bv_logic_options

qf_logic_options = qf_int_logic_options + \
    qf_real_logic_options + qf_bv_logic_options
qf_logic_options.append('BOOL')
qf_logic_options.append('QF_UF')
q_logic_options = q_int_logic_options + \
    q_real_logic_options + q_bv_logic_options
q_logic_options.append('QBF')
q_logic_options.append('UF')

string_logic_options = ['QF_S', 'QF_SLIA', 'QF_SNIA', 'QF_SLIRA', 'QF_UFSLIA']

total_logic_options = qf_logic_options + q_logic_options
total_logic_options += string_logic_options


class Op:
    """
    The Op class represents an operation in the SMT-LIB2 formula.
    It contains the node type and the expression associated with the operation.
    """

    def __init__(self, node, expr):
        self.expr = expr
        self.node = node

    def __repr__(self):
        return '({} {})'.format(self.node, self.expr)

    def __eq__(self, other):
        return isinstance(
            other, Op) and self.expr == other.expr and self.node == other.node

    def __hash__(self):
        return hash((self.expr, self.node))

    def get_node_ty(self):
        return self.node

    def set_node_ty(self, newnode):
        self.node = newnode


class IteOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class RegularOp(Op):  # regular exp
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class QuantifierOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class BoolOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class USortOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class IntOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class RealOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class FPOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class SetOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class BagOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class SeplogOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class StringOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class SeqOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class BVOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class ArrOp(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)


class Var:
    def __init__(self, sort, n):
        self.sort = sort
        self.n = n

    def __repr__(self):
        return str(self.sort) + str(self.n)


class VarBool(Var):
    def __init__(self, n):
        Var.__init__(self, 'v', n)

    def __eq__(self, other):
        return isinstance(other, VarBool) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarInt(Var):
    def __init__(self, n):
        Var.__init__(self, 'i', n)

    def __eq__(self, other):
        return isinstance(other, VarInt) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarReal(Var):
    def __init__(self, n):
        Var.__init__(self, 'r', n)

    def __eq__(self, other):
        return isinstance(other, VarReal) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarFP(Var):
    def __init__(self, n):
        Var.__init__(self, 'fpv', n)

    def __eq__(self, other):
        return isinstance(other, VarFP) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarSet(Var):
    def __init__(self, n):
        Var.__init__(self, 'st', n)

    def __eq__(self, other):
        return isinstance(other, VarSet) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarBag(Var):
    def __init__(self, n):
        Var.__init__(self, 'bag', n)

    def __eq__(self, other):
        return isinstance(other, VarBag) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarString(Var):
    def __init__(self, n):
        Var.__init__(self, 'str', n)

    def __eq__(self, other):
        return isinstance(other, VarString) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarSeq(Var):
    def __init__(self, n):
        Var.__init__(self, 'seq', n)

    def __eq__(self, other):
        return isinstance(other, VarString) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class VarUnIntSort(Var):
    def __init__(self, sort, n):
        Var.__init__(self, sort, n)

    def __repr__(self):
        return '{}-{}'.format(self.sort, self.n)

    def __eq__(self, other):
        return isinstance(
            other, VarUnIntSort) and self.n == other.n and self.sort == other.sort

    def __hash__(self):
        return hash((self.sort, self.n))


class VarBV(Var):
    def __init__(self, sort, n):
        Var.__init__(self, sort, n)

    def __repr__(self):
        return 'bv_{}-{}'.format(self.sort, self.n)

    def __eq__(self, other):
        return isinstance(
            other, VarBV) and self.n == other.n and self.sort == other.sort

    def __hash__(self):
        return hash((self.sort, self.n))


class VarArr(Var):
    def __init__(self, sort_index, sort_element, n):
        Var.__init__(self, sort_index, n)
        self.sort_element = sort_element

    def __repr__(self):
        return 'arr-{}_{}-{}'.format(hash(self.sort),
                                     hash(self.sort_element), self.n)

    def __eq__(self, other):
        return isinstance(other,
                          VarArr) and self.n == other.n and self.sort == other.sort and \
            self.sort_element == other.sort_element

    def __hash__(self):
        return hash((self.sort, self.sort_element, self.n))


class VarQuant(Var):
    def __init__(self, n):
        Var.__init__(self, 'q', n)

    def __eq__(self, other):
        return isinstance(other, VarQuant) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class Sort:
    def __init__(self, sort):
        self.sort = sort

    def __repr__(self):
        return str(self.sort)


class Bool(Sort):
    def __init__(self):
        Sort.__init__(self, 'Bool')

    def __eq__(self, other):
        return isinstance(other, Bool)

    def __hash__(self):
        return hash(self.sort)


class BoolVar(Sort):
    def __init__(self):
        Sort.__init__(self, 'Bool')

    def __eq__(self, other):
        return isinstance(other, BoolVar)

    def __hash__(self):
        return hash(self.sort)


class Regular(Sort):
    def __init__(self):
        Sort.__init__(self, 're')

    def __eq__(self, other):
        return isinstance(other, Regular)

    def __hash__(self):
        return hash(self.sort)


class Quantifier(Sort):
    def __init__(self):
        Sort.__init__(self, 'qu')

    def __eq__(self, other):
        return isinstance(other, Quantifier)

    def __hash__(self):
        return hash(self.sort)


class Int(Sort):
    def __init__(self):
        Sort.__init__(self, 'Int')

    def __eq__(self, other):
        return isinstance(other, Int)

    def __hash__(self):
        return hash(self.sort)


class IntVar(Sort):
    def __init__(self):
        Sort.__init__(self, 'Int')

    def __eq__(self, other):
        return isinstance(other, IntVar)

    def __hash__(self):
        return hash(self.sort)


class Real(Sort):
    def __init__(self):
        Sort.__init__(self, 'Real')

    def __eq__(self, other):
        return isinstance(other, Real)

    def __hash__(self):
        return hash(self.sort)


class RealVar(Sort):
    def __init__(self):
        Sort.__init__(self, 'Real')

    def __eq__(self, other):
        return isinstance(other, RealVar)

    def __hash__(self):
        return hash(self.sort)


# TODO: allo more FP types
class FP(Sort):
    def __init__(self):
        # Sort.__init__(self, '(_ FloatingPoint  8  24)')
        if m_test_fp64:
            Sort.__init__(self, 'Float64')
        else:
            Sort.__init__(self, 'Float32')

    def __eq__(self, other):
        return isinstance(other, FP)

    def __hash__(self):
        return hash(self.sort)


class Set(Sort):
    def __init__(self):
        Sort.__init__(self, '(Set Int)')

    def __eq__(self, other):
        return isinstance(other, Set)

    def __hash__(self):
        return hash(self.sort)


class Bag(Sort):
    def __init__(self):
        Sort.__init__(self, '(Bag Int)')

    def __eq__(self, other):
        return isinstance(other, Bag)

    def __hash__(self):
        return hash(self.sort)


class String(Sort):
    def __init__(self):
        Sort.__init__(self, '(String)')

    def __eq__(self, other):
        return isinstance(other, String)

    def __hash__(self):
        return hash(self.sort)


class Seq(Sort):
    def __init__(self):
        Sort.__init__(self, '(Seq Int)')

    def __eq__(self, other):
        return isinstance(other, Seq)

    def __hash__(self):
        return hash(self.sort)


class UnIntSort(Sort):
    def __init__(self, n):
        Sort.__init__(self, 'S')
        self.n = n

    def __repr__(self):
        return str(self.sort) + str(self.n)

    def __eq__(self, other):
        return isinstance(other, UnIntSort) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))


class BV(Sort):
    def __init__(self, w):
        Sort.__init__(self, 'BV')
        self.w = w

    def __repr__(self):
        return '(_ BitVec {})'.format(self.w)

    def __eq__(self, other):
        return isinstance(other, BV) and self.w == other.w

    def __hash__(self):
        return hash((self.sort, self.w))


class Arr(Sort):
    def __init__(self, sort_index, sort_element):
        Sort.__init__(self, 'Arr')
        self.sort_index = sort_index
        self.sort_element = sort_element

    def __repr__(self):
        return '(Array {} {})'.format(self.sort_index, self.sort_element)

    def __eq__(self, other):
        return isinstance(
            other,
            Arr) and self.sort_index == other.sort_index and self.sort_element == other.sort_element

    def __hash__(self):
        return hash((self.sort, self.sort_index, self.sort_element))


def random_real():
    y = 0
    if random.random() < 0.8:
        real = str(random.randint(1, 9))
    else:
        real = "0."
        y += 1
    for x in range(random.randint(0, 10)):
        if random.random() < 0.05 and y == 0:
            real += "."
            y += 1
        else:
            real += str(random.randint(0, 9))
    if real[-1] == ".":
        real += "0"
    # NOTE: Fix an important z3 paring error??. A real number should be 2.0,
    # not 2
    if "." not in real:
        real += ".0"
    return real


def get_random_unicode(length):
    """
    Generate a random Unicode string of the specified length.

    Args:
        length (int): The length of the generated Unicode string.

    Returns:
        str: A random Unicode string of the specified length.
    """

    try:
        get_char = unichr
    except NameError:
        get_char = chr
    # Update this to include code point ranges to be sampled
    include_ranges = [
        (0x0021, 0x0021),
        (0x0023, 0x0026),
        (0x0028, 0x007E),
        (0x00A1, 0x00AC),
        (0x00AE, 0x00FF),
        (0x0100, 0x017F),
        (0x0180, 0x024F),
        (0x2C60, 0x2C7F),
        (0x16A0, 0x16F0),
        (0x0370, 0x0377),
        (0x037A, 0x037E),
        (0x0384, 0x038A),
        (0x038C, 0x038C),
    ]

    alphabet = [
        get_char(code_point) for current_range in include_ranges
        for code_point in range(current_range[0], current_range[1] + 1)
    ]
    return ''.join(random.choice(alphabet) for _ in range(length))


def random_string():
    """
    Generate a random string
    """
    letters = string.ascii_uppercase
    letters += string.ascii_lowercase
    letters += string.digits  # number
    # if random.random() < 0.15: letters += ';.<>+-/_{}=?'
    length = random.randint(1, 15)
    # letters = string.digits + string.ascii_letters + string.punctuation #
    # alread cover uniocode and xx?
    if m_test_string_unicode:
        sp = random.random()
        if sp < 0.45:
            return ''.join(random.choice(letters) for _ in range(length))
        elif sp < 0.85:
            bytes_data = get_random_unicode(length).encode('unicode-escape')
            return "".join(map(chr, bytes_data))
        else:
            return ""
    else:
        if random.random() < 0.85:
            return ''.join(random.choice(letters) for _ in range(length))
        else:
            return ""


# TODO !!!!!!!!!! This function is buggy? How to generate random fp???
def random_fp():
    y = 0
    if random.random() < 0.8:
        real = str(random.randint(1, 9))
    else:
        real = "0."
        y += 1
    for x in range(random.randint(0, 10)):
        if random.random() < 0.05 and y == 0:
            real += "."
            y += 1
        else:
            real += str(random.randint(0, 9))
    if real[-1] == ".":
        real += "0"
    if "." not in real:
        real += ".0"

    if m_fp_rounding_mode == 'random':
        pp = random.random()
        if pp < 0.2:
            rrr = " RNE "
        elif pp < 0.4:
            rrr = " RNA "
        elif pp < 0.6:
            rrr = " RTP "
        elif pp < 0.8:
            rrr = " RTN "
        else:
            rrr = " RTZ "

        if m_test_fp64:
            fp = "((_ to_fp 11 53)" + rrr + real + ")"
        else:
            fp = "((_ to_fp 8 24)" + rrr + real + ")"
        return fp
    else:
        if m_test_fp64:
            fp = "((_ to_fp 11 53) " + m_fp_rounding_mode + " " + real + ")"
        else:
            fp = "((_ to_fp 8 24) " + m_fp_rounding_mode + " " + real + ")"
        return fp


def random_BV():
    prob = random.random()
    # num = random.randint(0, 8000)
    num = random.randint(0, 100)
    if prob < 0.33:
        if random.random() < 0.5:
            bv = "#b" + str(bin(num)[2:])
            width = len(str(bin(num)[2:]))
        else:
            bv = "#b0" + str(bin(num)[2:])
            width = len(str(bin(num)[2:])) + 1
    elif prob < 0.66:
        bv = "#x" + str(hex(num)[2:])
        width = len(str(hex(num)[2:])) * 4
    else:
        width = len(str(bin(num)[2:]))
        bv = "(_ bv{} {})".format(num, width)
    return bv, width


def Ratio(lower_bound, upper_bound, ratio):
    n_variables = random.randint(lower_bound, upper_bound)
    n_clauses = math.ceil(ratio * n_variables)
    return n_variables, n_clauses


def find(s, ch):
    return [ii for ii, ltr in enumerate(s) if ltr == ch]


def replace_idx(s, index, replacement):
    return '{}{}{}'.format(s[:index], replacement, s[index + 1:])


def set_options():
    global m_test_proof, m_test_unsat_core

    if m_optionmode == 'none':
        return

    if m_test_proof:
        print("(set-option :produce-proofs true)")
    if m_test_unsat_core:
        print('(set-option :produce-unsat-cores true)')


def set_logic(logic_choice):
    global m_quantifier_rate, m_test_set_bapa, m_test_bag_bapa, m_test_my_uf, m_test_string
    global m_set_logic
    if 'UF' in logic_choice or logic_choice == 'ALL':
        if random.random() < 0.5:
            m_test_my_uf = True
    if 'IDL' in logic_choice or 'RDL' in logic_choice:
        # NOTE!! dangerous operation; I disable all possible non-linear funcs
        global IntBinOp
        global IntNOp
        global RealBinOp
        global RealNOp
        IntBinOp = ["-", "+"]
        IntNOp = ["-", "+"]
        RealBinOp = ["-", "+"]
        RealNOp = ["-", "+"]

    # For testing horn tactic, generate more quantifiers
    if m_test_datalog_chc_as_tactic:
        m_quantifier_rate = 0.33

    a = m_create_exp_rate  # newSort
    b = 0.66  # varUSort
    # c = 1  # bool_from_usort
    c = m_create_bool_rate
    # ni = m_create_exp_rate  # new_int
    ni = m_declare_new_var_rate
    e = m_create_exp_rate  # int_from_int
    # f = m_create_exp_rate  # bool_from_int
    f = m_create_bool_rate
    # g = m_create_exp_rate  # new_real
    g = m_declare_new_var_rate
    h = m_create_exp_rate  # real_from_real
    # m = m_create_exp_rate  # bool_from_real
    m = m_create_bool_rate
    v = m_create_exp_rate  # real_and_int
    # r = m_create_exp_rate  # new_BV
    r = m_declare_new_var_rate
    t = m_create_exp_rate  # BV_from_BV
    # u = m_create_exp_rate  # bool_from_BV
    u = m_create_bool_rate
    gen_arr = m_create_exp_rate  # arrays of any sort
    add_reals = 0
    add_ints = 0
    add_quantifiers = -1

    # not supported by z3: ANIA, 'ANRA', 'QF_ANRA', 'QF_ALRA', 'QF_AUFNRA', "QF_AUFLRA', "UFNRA', 'AUFLRA'??
    # why no AX?  'QF_AX', 'AX'

    if logic_choice == 'ALL':
        if m_set_logic:
            print('(set-logic ALL)')
        set_options()
        add_reals = 1
        add_ints = 1
        if random.random() < 0.33:
            r, t, u = -1, -1, -1  # no BV
        if random.random() < 0.33:
            g, h, m, v = -1, -1, -1, -1
            add_reals = -1
        if random.random() < 0.33:
            ni, e, f, v = -1, -1, -1, -1
            add_ints = -1
        elif random.random() < 0.15:
            m_test_set_bapa = True
        if random.random() < 0.33:
            add_quantifiers = m_quantifier_rate

    elif logic_choice == 'BVINT':
        # if m_set_logic: print('(set-logic ALL)')
        set_options()
        add_ints = 1
        g, h, m, v = -1, -1, -1, -1
        add_reals = -1  # no real
        # ni, e, f, v = -1, -1, -1, -1; add_ints = -1 # keep int
        if random.random() < 0.33:
            add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_ABV':
        if m_set_logic:
            print('(set-logic QF_ABV)')
        set_options()
        a, b, c, ni, e, f, g, h, m, v, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate

    elif logic_choice == 'QF_BV':
        if m_set_logic:
            print('(set-logic QF_BV)')
        set_options()
        a, b, c, ni, e, f, g, h, m, v, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_AUFBV':
        if m_set_logic:
            print('(set-logic QF_AUFBV)')
        set_options()
        ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate

    elif logic_choice == 'QF_NIA':
        if m_set_logic:
            print('(set-logic QF_NIA)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'QF_ANIA':
        if m_set_logic:
            print('(set-logic QF_ANIA)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1

    elif logic_choice == 'QF_LIA':
        if m_set_logic:
            print('(set-logic QF_LIA)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'QF_IDL':
        if m_set_logic:
            print('(set-logic QF_IDL)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'QF_UFIDL':
        if m_set_logic:
            print('(set-logic QF_UFIDL)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'IDL':
        if m_set_logic:
            print('(set-logic IDL)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_ALIA':
        if m_set_logic:
            print('(set-logic QF_ALIA)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1

    elif logic_choice == 'QF_UFLIA':
        if m_set_logic:
            print('(set-logic QF_UFLIA)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'QF_AUFLIA':
        if m_set_logic:
            print('(set-logic QF_AUFLIA)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1

    elif logic_choice == 'QF_NRA':
        if m_set_logic:
            print('(set-logic QF_NRA)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_NRAT':
        if m_set_logic:
            print('(set-logic QF_NRAT)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    # TODO: here I use the same setting of QF_NRA for QF_FP, which is not good
    # (missing many fp operations)
    elif logic_choice == 'QF_FP':
        if m_set_logic:
            print('(set-logic QF_FP)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'FP':
        if m_set_logic:
            print('(set-logic FP)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    # FP + Real
    elif logic_choice == 'QF_FPLRA':
        if m_set_logic:
            print('(set-logic QF_FPLRA)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'FPLRA':
        # if m_set_logic: print('(set-logic FPLRA)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_LRA':
        if m_set_logic:
            print('(set-logic QF_LRA)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_RDL':
        if m_set_logic:
            print('(set-logic QF_RDL)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_UFRDL':
        if m_set_logic:
            print('(set-logic QF_UFRDL)')
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_UFLRA':
        if m_set_logic:
            print('(set-logic QF_UFLRA)')
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_ALRA':
        if m_set_logic:
            print('(set-logic QF_AUFLIRA)')  # a trick for z3 to recognize
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1

    elif logic_choice == 'QF_AUFLRA':
        if m_set_logic:
            print('(set-logic QF_AUFLIRA)')  # a trick for z3 to recognize
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1

    elif logic_choice == 'QF_ANRA':
        if m_set_logic:
            print('(set-logic QF_AUFNIRA)')  # a trick for z3 to recognize
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1
        a, b, c = -1, -1, -1

    elif logic_choice == 'QF_AUFNRA':
        if m_set_logic:
            print('(set-logic QF_AUFNIRA)')  # a trick for z3 to recognize
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1

    elif logic_choice == 'QF_UF':
        if m_set_logic:
            print('(set-logic QF_UF)')
        set_options()
        ni, e, f, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_UFC':
        if m_set_logic:
            print('(set-logic QF_UFC)')
        set_options()
        ni, e, f, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'UFC':
        if m_set_logic:
            print('(set-logic UFC)')
        set_options()
        ni, e, f, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_UFBV':
        if m_set_logic:
            print('(set-logic QF_UFBV)')
        set_options()
        ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_UFNRA':
        if m_set_logic:
            print('(set-logic QF_UFNRA)')
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_UFNIA':
        if m_set_logic:
            print('(set-logic QF_UFNIA)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'QF_AUFNIA':
        if m_set_logic:
            print('(set-logic QF_AUFNIA)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1

    elif logic_choice == 'QF_ABV':
        if m_set_logic:
            print('(set-logic QF_ABV)')
        set_options()
        a, b, c, ni, e, f, g, h, m, v = -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_AUFBV':
        if m_set_logic:
            print('(set-logic QF_AUFBV)')
        set_options()
        ni, e, f, g, h, m, v = -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'ABV':
        if m_set_logic:
            print('(set-logic ABV)')
        set_options()
        a, b, c, ni, e, f, g, h, m, v, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'BV':
        if m_set_logic:
            print('(set-logic BV)')
        set_options()
        a, b, c, ni, e, f, g, h, m, v, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'AUFBV':
        if m_set_logic:
            print('(set-logic AUFBV)')
        set_options()
        ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'NIA':
        if m_set_logic:
            print('(set-logic NIA)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'ANIA':
        if m_set_logic:
            print('(set-logic AUFNIRA)')  # a trick for z3 to recognize
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'AUFNIA':
        if m_set_logic:
            print('(set-logic AUFNIRA)')  # a trick for z3 to recognize
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'AUFLIA':
        if m_set_logic:
            print('(set-logic AUFLIA)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'ALIA':
        if m_set_logic:
            print('(set-logic ALIA)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'LIA':
        if m_set_logic:
            print('(set-logic LIA)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'NRA':
        if m_set_logic:
            print('(set-logic NRA)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'LRA':
        if m_set_logic:
            print('(set-logic LRA)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'ANRA':
        if m_set_logic:
            print('(set-logic AUFNIRA)')  # a trick for z3 to recognize
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'AUFNRA':
        if m_set_logic:
            print('(set-logic AUFNIRA)')  # a trick for z3 to recognize
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    # lira_logics = ['QF_LIRA', 'LIRA', 'QF_ALIRA', 'ALIRA', 'QF_UFLIRA', 'UFLIRA', 'QF_AUFLIRA', 'AUFLIRA']
    # nira_logics = ['QF_NIRA', 'NIRA', 'QF_ANIRA', 'ANIRA', 'QF_UFNIRA',
    elif 'IRA' in logic_choice:
        if m_set_logic:
            print('(set-logic ' + logic_choice + ')')
        set_options()
        if 'QF' not in logic_choice:
            add_quantifiers = m_quantifier_rate
        add_reals = 1
        add_ints = 1
        v = m_create_exp_rate

        if logic_choice in ['QF_LIRA', 'QF_NIRA', 'LIRA', 'NIRA', 'QF_SLIRA']:
            a, b, c, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1

        elif logic_choice in ['QF_ALIRA', 'QF_ANIRA', 'ALIRA', 'ANIRA']:
            a, b, c, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, m_create_exp_rate

        elif logic_choice in ['QF_UFLIRA', 'QF_UFNIRA', 'UFLIRA', 'UFNIRA']:
            r, t, u, gen_arr = -1, -1, -1, -1

        elif logic_choice in ['QF_AUFLIRA', 'QF_AUFNIRA', 'AUFLIRA', 'AUFNIRA']:
            r, t, u, gen_arr = -1, -1, -1, 0.33

    elif logic_choice == 'AUFLRA':
        if m_set_logic:
            print('(set-logic AUFLIRA)')  # a trick for z3 to recognize
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'ALRA':
        if m_set_logic:
            print('(set-logic AUFLIRA)')  # a trick for z3 to recognize
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = -1, -1, - \
            1, -1, -1, -1, -1, -1, -1, -1, m_create_exp_rate
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'RDL':
        if m_set_logic:
            print('(set-logic RDL)')
        set_options()
        a, b, c, ni, e, f, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'UF':
        if m_set_logic:
            print('(set-logic UF)')
        set_options()
        ni, e, f, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'UFBV':
        if m_set_logic:
            print('(set-logic UFBV)')
        set_options()
        ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'UFNRA':
        if m_set_logic:
            print('(set-logic UFNRA)')
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'UFLRA':
        if m_set_logic:
            print('(set-logic UFLRA)')
        set_options()
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'UFNIA':
        if m_set_logic:
            print('(set-logic UFNIA)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'UFLIA':
        if m_set_logic:
            print('(set-logic UFLIA)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'AX':
        if m_set_logic:
            print('(set-logic AX)')
        set_options()
        add_reals = 1
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_BOOL' or logic_choice == 'BOOL':  # pure SAT
        if m_set_logic:
            print('(set-logic QF_UF)')  # should we?
        # else: if m_set_logic: print('(set-logic BV)')
        set_options()
        a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QBF':  # QBF
        if m_set_logic:
            print('(set-logic UF)')  # should we?
        # else: if m_set_logic: print('(set-logic BV)')
        set_options()
        a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'SET':
        if m_set_logic:
            print('(set-logic ALL)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        # TODO: should we enable quantifier for BAPA?
        # NOTE: BAPA does not support model generation?
        if random.random() < 0.3:
            add_reals = 1
            g, h, m, v, = m_create_exp_rate, m_create_exp_rate, m_create_exp_rate, m_create_exp_rate
        if random.random() < 0.5:
            add_quantifiers = m_quantifier_rate

    elif logic_choice == 'STRSET':
        if m_set_logic:
            print('(set-logic ALL)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        if random.random() < 0.3:
            add_reals = 1
            g, h, m, v, = m_create_exp_rate, m_create_exp_rate, m_create_exp_rate, m_create_exp_rate

    # TODO: make QF_S and QF_SLIA different
    elif logic_choice == 'QF_S':
        if m_set_logic:
            print('(set-logic QF_S)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1  #
        # if random.random() < 0.5: add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QSTR':
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_SLIA':
        # if random.random() < 0.5: if m_set_logic: print('(set-logic QF_SLIA)')
        # else: if m_set_logic: print('(set-logic ALL)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'SEQ':
        # if random.random() < 0.5:
        #    if m_set_logic: print('(set-logic QF_SLIA)')
        # else:
        #    if m_set_logic: print('(set-logic ALL)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        # if random.random() < 0.5: add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_UFSLIA':
        # if random.random() < 0.5: if m_set_logic: print('(set-logic QF_UFSLIA)')
        # else: if m_set_logic: print('(set-logic ALL)')
        set_options()
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        # if random.random() < 0.5: add_quantifiers = m_quantifier_rate

    elif logic_choice == 'QF_SNIA':
        # if m_set_logic: print('(set-logic ALL)')
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        # if random.random() < 0.5: add_quantifiers = m_quantifier_rate

    elif logic_choice == 'SEPLOG':
        set_options()
        a, b, c, g, h, m, v, r, t, u, gen_arr = - \
            1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1
        # add_quantifiers = m_quantifier_rate

    return a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals, add_quantifiers


class Clauses:
    def __init__(self, b, nc):
        int_nc = int(nc)
        self.n_clauses = int_nc
        self.clauses = []
        self.unused_options = list(b)
        self.all_options = list(b)

    def new_cnfs(self):
        global m_assert_id, m_all_assertions
        for i in range(self.n_clauses):
            cnf = "(or "
            cls_size = 0
            for j in range(2):
                n_left = ((self.n_clauses - i) * 3) + (3 - j)
                if len(self.unused_options) == n_left:
                    addition = random.choice(self.unused_options)
                    cnf += (str(addition) + " ")
                    cls_size += 1
                    self.unused_options.remove(addition)
                else:
                    addition = random.choice(self.all_options)
                    cnf += (str(addition) + " ")
                    cls_size += 1
                    if addition in self.unused_options:
                        self.unused_options.remove(addition)
            n_left = ((self.n_clauses - i) * 3) + (3 - j)
            if len(self.unused_options) == n_left:
                addition = random.choice(self.unused_options)
                cnf += (str(addition) + ")")
                cls_size += 1
            else:
                addition = random.choice(self.all_options)
                cnf += (str(addition) + ")")
                cls_size += 1
            self.clauses.append(cnf)

            if m_test_max_smt or m_test_max_sat:
                if random.random() < m_max_smt_rate:
                    print('(assert ' + cnf + ')')
                else:
                    # (assert -soft (= 0 0) :weight 1)
                    # print('(assert-soft ' + cnf + ')')
                    print('(assert-soft ' + cnf + ' :weight ' +
                          str(random.randint(1, 20)) + ' )')
            elif m_test_unsat_core or m_test_proof or m_test_named_assert:
                m_assert_id += 1
                print(
                    '(assert (! (or ' + cnf + ' false) :named IP_' + str(m_assert_id) + '))')
                m_all_assertions.append('IP_' + str(m_assert_id))

            else:
                print('(assert (or ' + cnf + ' false))')

    def new_dist_cnfs(self):
        global m_assert_id, m_all_assertions
        n_slots = (self.n_clauses * 3)
        tmp_string = ""
        for ith in range(n_slots - 1):
            n_left = n_slots - ith
            if len(self.unused_options) == n_left:
                addition = random.choice(self.unused_options)
                tmp_string += (str(addition) + "$")
                self.unused_options.remove(addition)
            else:
                addition = random.choice(self.all_options)
                tmp_string += (str(addition) + "$")
                if addition in self.unused_options:
                    self.unused_options.remove(addition)
        if len(self.unused_options) == 1:
            addition = random.choice(self.unused_options)
            tmp_string += str(addition)
        else:
            addition = random.choice(self.all_options)
            tmp_string += str(addition)

        place_holders = find(tmp_string, '$')
        w = n_slots - (self.n_clauses - 1)
        spaces = random.sample(place_holders, w)
        for x in spaces:
            tmp_string = replace_idx(tmp_string, x, ' ')
        partitions = find(tmp_string, '$')
        cnf_s = []
        for x in partitions:
            c = tmp_string[:x]
            q = c.rfind('$')
            if q >= 0:
                c = c[q + 1:]
            cnf_s.append(c)
        for items in cnf_s:
            new_cnf = '(or {} false)'.format(items)  # corrent?
            # print("; new_dist_cnfs")
            self.clauses.append(new_cnf)
            if m_test_max_smt or m_test_max_sat:
                if random.random() < m_max_smt_rate:
                    print('(assert {})'.format(new_cnf))
                else:
                    print('(assert-soft {} :weight {})'.format(new_cnf,
                          str(random.randint(1, 20))))
            elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                m_assert_id += 1
                print(
                    '(assert (! ' +
                    format(new_cnf) +
                    ' :named IP_' +
                    str(m_assert_id) +
                    '))')
                m_all_assertions.append('IP_' + str(m_assert_id))
            else:
                print('(assert {})'.format(new_cnf))

    def cnf_choice(self):
        return random.choice(self.clauses)

    def node_from_cnf(self):
        n_operands = random.randint(1, 10)
        operands = str(random.choice(self.clauses))
        for _ in range(n_operands):
            operands += (" " + str(random.choice(self.clauses)))
        # TODO; seems bugs here: too many 'or' in the smt2 files
        # thus, I add a number m_or_and_rate
        if random.random() < 0.5:
            n_and = operands.count('and')
            n_or = operands.count('or')
            if n_and > n_or:
                new_cnf = Op('or', operands)
            elif n_and < n_or:
                new_cnf = Op('and', operands)
            else:
                if random.random() < 0.5:
                    new_cnf = Op('or', operands)
                else:
                    new_cnf = Op('and', operands)
        else:
            # if random.random() < 1: new_cnf = Op('or', operands)
            if random.random() < m_or_and_rate:
                new_cnf = Op('or', operands)
            else:
                new_cnf = Op('and', operands)

        self.clauses.append(new_cnf)
        return new_cnf

    def bin_node(self):
        op1 = '{} {}'.format(
            random.choice(
                self.clauses), random.choice(
                self.clauses))
        op2 = '{} {}'.format(
            random.choice(
                self.clauses), random.choice(
                self.clauses))
        new_cnf1 = Op('=>', op1)
        new_cnf2 = Op('or', op2)
        self.clauses.append(new_cnf1)
        self.clauses.append(new_cnf2)
        return new_cnf1, new_cnf2


class SimpleNodes:
    def __init__(self, init_vars, ty):
        self.d = OrderedDict()
        self.d[Bool()] = []
        self.d[Int()] = []
        self.d[Real()] = []
        self.d[String()] = []
        self.dict = OrderedDict()
        self.dict[Bool()] = 0
        self.dict[Int()] = 0
        self.dict[Real()] = 0
        self.dict[String()] = 0
        self.new_keys = []
        self.indices = []

        if m_test_datalog_chc:
            global IntBinOp
            global IntNOp
            global RealBinOp
            global RealNOp
            IntBinOp = ["-", "+"]
            IntNOp = ["-", "+"]
            RealBinOp = ["-", "+"]
            RealNOp = ["-", "+"]

        if ty == "Int":
            for variable in init_vars:
                self.d[Int()].append(variable)
            self.d[Int()].append(str(random.randint(0, 5000)))
            self.d[Int()].append(str(random.randint(0, 5000)))
            for _ in range(15):
                self.int_from_int()
                self.bool_from_int()
        elif ty == "Real":
            for variable in init_vars:
                self.d[Real()].append(variable)
            self.d[Real()].append(str(random.randint(0, 5000)))
            self.d[Real()].append(str(random.randint(0, 5000)))
            for _ in range(15):
                self.real_from_real()
                self.bool_from_real()
        elif ty == "String":
            for variable in init_vars:
                self.d[String()].append(variable)
            for _ in range(15):
                self.string_from_string()

    def get_int_term(self):
        return random.choice(self.d[Int()])

    def get_real_term(self):
        return random.choice(self.d[Real()])

    def get_string_term(self):
        return random.choice(self.d[String()])

    def get_bool(self):
        return random.choice(self.d[Bool()])

    def string_from_string(self):
        chance = random.random()
        if chance < 0.1:  # unary
            new_str = "\"" + random_string() + "\""
            self.d[String()].append(new_str)
        elif chance < 0.45:  # binary
            par = random.choice(self.d[String()])
            operands = str(par)
            par = random.choice(self.d[String()])
            operands += (" " + str(par))
            new_str = StringOp(random.choice(StringBinOp), operands)
            self.d[String()].append(new_str)
        else:
            par = random.choice(self.d[String()])
            operands = str(par)
            n = random.randrange(1, 5)
            for _ in range(n):
                if random.random() < 0.7:
                    par = random.choice(self.d[String()])
                    operands += (" " + str(par))
                else:
                    substr = random_string()
                    operands += (" " + "\"" + substr + "\"")
            op_to_use = random.choice(StringNOp)
            new_str = StringOp(op_to_use, operands)
            self.d[String()].append(new_str)

    def bool_from_string(self):
        chance = random.random()
        if chance < 0.5:
            par = random.choice(self.d[String()])
            operands = str(par)
            par = random.choice(self.d[String()])
            operands += (" " + str(par))
            new_bool = BoolOp(random.choice(StringBinBoolOp), operands)
            self.d[Bool()].append(new_bool)
        else:
            par = random.choice(self.d[String()])
            operands = str(par)
            op_to_use = random.choice(StringNBoolOp)
            n = random.randrange(1, 5)
            for _ in range(n):
                if random.random() < 0.9:
                    par = random.choice(self.d[String()])
                    operands += (" " + str(par))
                else:
                    if op_to_use == "distinct":
                        substr = random_string()
                        operands += (" " + "\"" + substr + "\"")
                    else:
                        par = random.choice(self.d[String()])
                        operands += (" " + str(par))
            new_bool = BoolOp(op_to_use, operands)
            self.d[Bool()].append(new_bool)

    def int_from_int(self):
        p = random.random()
        if p < 0.3:
            par = random.choice(self.d[Int()])
            new_int = IntOp(random.choice(IntUnOp), par)
            self.d[Int()].append(new_int)
        elif p < 0.66:
            par = random.choice(self.d[Int()])
            operand = str(par)
            par2 = random.choice(self.d[Int()])
            operand += (" " + str(par2))
            new_int = IntOp(random.choice(IntBinOp), operand)
            self.d[Int()].append(new_int)
        else:
            par = random.choice(self.d[Int()])
            operand = str(par)
            n = random.randrange(1, 5)
            for _ in range(n):
                par = random.choice(self.d[Int()])
                operand += (" " + str(par))
            op_to_use = random.choice(IntNOp)
            new_int = IntOp(op_to_use, operand)
            self.d[Int()].append(new_int)

    def bool_from_int(self):
        if random.random() < 0.66:  # seems the old strategy is "better"?
            par = random.choice(self.d[Int()])
            operand = str(par)
            par = random.choice(self.d[Int()])
            operand += (" " + str(par))
            new_bool = BoolOp(random.choice(IRNBoolOp), operand)
            self.d[Bool()].append(new_bool)
            return  # stop here
        par = random.choice(self.d[Int()])
        operands = str(par)
        n_operands = random.randrange(1, 6)
        for _ in range(n_operands):
            par = random.choice(self.d[Int()])
            operands += (" " + str(par))
        new_bool = BoolOp(random.choice(IRNBoolOp), operands)
        self.d[Bool()].append(new_bool)

    def real_from_real(self):
        p = random.random()
        if p < 0.3:
            par = random.choice(self.d[Real()])
            new_r = RealOp(random.choice(RealUnOp), par)
            self.d[Real()].append(new_r)
        elif p < 0.66:
            par = random.choice(self.d[Real()])
            operand = str(par)
            par2 = random.choice(self.d[Real()])
            operand += (" " + str(par2))
            new_r = RealOp(random.choice(RealBinOp), operand)
            self.d[Real()].append(new_r)
        else:
            par = random.choice(self.d[Real()])
            operand = str(par)
            n = random.randrange(1, 5)
            for _ in range(n):
                par = random.choice(self.d[Real()])
                operand += (" " + str(par))
            new_r = RealOp(random.choice(RealNOp), operand)
            self.d[Real()].append(new_r)

    def bool_from_real(self):
        par = random.choice(self.d[Real()])
        operands = str(par)
        n_operands = random.randrange(1, 6)
        for _ in range(n_operands):
            par = random.choice(self.d[Real()])
            operands += (" " + str(par))
        new_bool = BoolOp(random.choice(IRNBoolOp), operands)
        self.d[Bool()].append(new_bool)


class Nodes:
    def __init__(self, a_ints, a_reals):
        self.d = OrderedDict()
        self.d[Bool()] = []

        self.nq = 0
        self.qdict = OrderedDict()

        # dictionary of number of all nodes ever created
        self.dict = OrderedDict()
        self.dict[Bool()] = 0
        self.dict[Int()] = 0
        self.dict[Real()] = 0

        self.initial_ints = a_ints
        self.initial_reals = a_reals

        self.new_keys = []
        self.indices = []

        self.n_vars = random.randint(1, 6)
        self.n_ints = random.randint(1, 20)
        self.n_reals = random.randint(1, 20)

        self.initial_bvs = 0  # bv
        self.n_bvs = 0

        # just for storing quantified exp? (TODO: not so easy, because we need to manager it at push/pop
        # self.dict[Quantifier()] = 1
        # self.d[Quantifier()] = []

        if (m_test_fp or m_test_fp_lra) and (not m_test_datalog_chc):
            self.dict[FP()] = 0
            self.initial_fps = 1
            self.n_fps = random.randint(1, 20)
            self.d[FP()] = []

            self.initial_ints = 0

            if not m_test_fp_lra:
                self.initial_reals = 0

            for ith in range(self.n_fps):
                if not m_test_fp_no_num and random.random() < 0.4:
                    new_fp = random_fp()
                    self.d[FP()].append(new_fp)
                    self.dict[FP()] += 1
                else:
                    self.d[FP()].append(VarFP(ith))
                    if m_test_fp64:
                        print('(declare-fun {} () Float64)'.format(VarFP(ith)))
                    else:
                        print('(declare-fun {} () Float32)'.format(VarFP(ith)))
                    self.dict[FP()] += 1
            if m_test_fp64:  # special FP constants
                self.d[FP()].append("(_ +oo 11 53)")
                self.d[FP()].append("(_ -oo 11 53)")
                self.d[FP()].append("(_ +zero 11 53)")
                self.d[FP()].append("(_ -zero 11 53)")
                self.d[FP()].append("(_ NaN 11 53)")
            else:
                self.d[FP()].append("(_ +oo 8 24)")
                self.d[FP()].append("(_ -oo 8 24)")
                self.d[FP()].append("(_ +zero 8 24)")
                self.d[FP()].append("(_ +zero 8 24)")
                self.d[FP()].append("(_ NaN 8 24)")

        if m_test_datalog_chc:
            self.int_funcs = []
            self.real_funcs = []
            self.bv_funcs = []

            # (declare-fun inv-int1 (Real Real ) Bool)
            self.n_vars = 3
            if m_test_datalog_chc_logic == "int":
                self.initial_ints = 1
                self.initial_reals = 0
                self.initial_bvs = 0
                self.n_ints = 5
            elif m_test_datalog_chc_logic == "real":
                self.initial_reals = 1
                self.initial_ints = 0
                self.initial_bvs = 0
                self.n_reals = 5
            elif m_test_datalog_chc_logic == "bv":
                self.initial_bvs = 1
                self.initial_ints = 0
                self.initial_reals = 0
                self.n_bvs = 8

            '''
            if self.initial_ints > 0:
                self.int_funcs.append("inv-int1")
                self.int_funcs.append("inv-int2")
                self.int_funcs.append("inv-int3")
                print("(declare-fun inv-int1 (Int Int) Bool)")
                print("(declare-fun inv-int2 (Int Int Int) Bool)")
                print("(declare-fun inv-int3 (Int Int Int Int) Bool)")

            elif self.initial_reals > 0:
                self.real_funcs.append("inv-real1")
                self.real_funcs.append("inv-real2")
                self.real_funcs.append("inv-real3")
                print("(declare-fun inv-real1 (Real Real) Bool)")
                print("(declare-fun inv-real2 (Real Real Real) Bool)")
                print("(declare-fun inv-real3 (Real Real Real Real) Bool)")
            '''
            return

        if m_test_my_uf:
            print("(declare-fun uf3 (Bool Bool Bool) Bool)")
            print("(declare-fun uf4 (Bool Bool Bool Bool) Bool)")
            print("(declare-fun uf5 (Bool Bool Bool Bool Bool) Bool)")
            print("(declare-fun uf6 (Bool Bool Bool Bool Bool Bool) Bool)")
            print("(declare-fun uf7 (Bool Bool Bool Bool Bool Bool Bool) Bool)")

            print("(declare-fun uf3_2 (Bool Bool Bool) Bool)")
            print("(declare-fun uf4_2 (Bool Bool Bool Bool) Bool)")
            print("(declare-fun uf5_2 (Bool Bool Bool Bool Bool) Bool)")
            print("(declare-fun uf6_2 (Bool Bool Bool Bool Bool Bool) Bool)")
            print("(declare-fun uf7_2 (Bool Bool Bool Bool Bool Bool Bool) Bool)")

        for ith in range(self.n_vars):
            self.d[Bool()].append(VarBool(ith))
            print('(declare-fun {} () Bool)'.format(VarBool(ith)))
            self.dict[Bool()] += 1

        if self.initial_ints == 1:
            self.d[Int()] = []
            for ith in range(self.n_ints):
                if random.random() < 0.5 and (not m_test_string):  # donot show Int for QF_S
                    self.d[Int()].append(VarInt(ith))
                    print('(declare-fun {} () Int)'.format(VarInt(ith)))
                else:
                    val = random.randint(0, 100)
                    self.d[Int()].append(val)
                self.dict[Int()] += 1

            if m_test_seplog:
                print("(declare-heap (Int Int))")
            if m_test_my_uf:
                print("(declare-fun ufib3 (Int Int Int) Bool)")
                print("(declare-fun ufib4 (Int Int Int Int) Bool)")
                print("(declare-fun ufib5 (Int Int Int Int Int) Bool)")
                print("(declare-fun ufib6 (Int Int Int Int Int Int) Bool)")
                print("(declare-fun ufib7 (Int Int Int Int Int Int Int) Bool)")

                print("(declare-fun ufbi3 (Bool Bool Bool) Int)")
                print("(declare-fun ufbi4 (Bool Bool Bool Bool) Int)")
                print("(declare-fun ufbi5 (Bool Bool Bool Bool Bool) Int)")
                print("(declare-fun ufbi6 (Bool Bool Bool Bool Bool Bool) Int)")
                print("(declare-fun ufbi7 (Bool Bool Bool Bool Bool Bool Bool) Int)")

                print("(declare-fun ufii3 (Int Int Int) Int)")
                print("(declare-fun ufii4 (Int Int Int Int) Int)")
                print("(declare-fun ufii5 (Int Int Int Int Int) Int)")
                print("(declare-fun ufii6 (Int Int Int Int Int Int) Int)")
                print("(declare-fun ufii7 (Int Int Int Int Int Int Int) Int)")

                print("(declare-fun ufii3_2 (Int Int Int) Int)")
                print("(declare-fun ufii4_2 (Int Int Int Int) Int)")
                print("(declare-fun ufii5_2 (Int Int Int Int Int) Int)")
                print("(declare-fun ufii6_2 (Int Int Int Int Int Int) Int)")
                print("(declare-fun ufii7_2 (Int Int Int Int Int Int Int) Int)")

        if self.initial_reals == 1:
            self.d[Real()] = []
            for ith in range(self.n_reals):
                if random.random() < 0.5:
                    self.d[Real()].append(VarReal(ith))
                    print('(declare-fun {} () Real)'.format(VarReal(ith)))
                else:
                    new_real = random_real()
                    self.d[Real()].append(new_real)
                self.dict[Real()] += 1
            if m_test_my_uf:
                print("(declare-fun ufrb3 (Real Real Real) Bool)")
                print("(declare-fun ufrb4 (Real Real Real Real) Bool)")
                print("(declare-fun ufrb5 (Real Real Real Real Real) Bool)")
                print("(declare-fun ufrb6 (Real Real Real Real Real Real) Bool)")
                print("(declare-fun ufrb7 (Real Real Real Real Real Real Real) Bool)")

                print("(declare-fun ufbr3 (Bool Bool Bool) Real)")
                print("(declare-fun ufbr4 (Bool Bool Bool Bool) Real)")
                print("(declare-fun ufbr5 (Bool Bool Bool Bool Bool) Real)")
                print("(declare-fun ufbr6 (Bool Bool Bool Bool Bool Bool) Real)")
                print("(declare-fun ufbr7 (Bool Bool Bool Bool Bool Bool Bool) Real)")

                print("(declare-fun ufrr3 (Real Real Real) Real)")
                print("(declare-fun ufrr4 (Real Real Real Real) Real)")
                print("(declare-fun ufrr5 (Real Real Real Real Real) Real)")
                print("(declare-fun ufrr6 (Real Real Real Real Real Real) Real)")
                print("(declare-fun ufrr7 (Real Real Real Real Real Real Real) Real)")

        if self.initial_bvs == 1:  # seems not used
            for ith in range(self.n_bvs):
                if random.random() < 0.25:
                    width = random.randint(1, 64)
                    # width = random.randint(10000, 100000)
                    bv_sort = BV(width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                        self.dict[bv_sort] = 0
                    const = VarBV(width, len(self.d[bv_sort]))
                    print('(declare-fun {} () {})'.format(const, bv_sort))
                    self.d[bv_sort].append(const)
                    self.dict[bv_sort] += 1
                else:
                    bv, width = random_BV()
                    bv_sort = BV(width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                        self.dict[bv_sort] = 0
                        self.d[bv_sort].append(bv)
                        self.dict[bv_sort] += 1

        if m_test_set_bapa:
            self.dict[Set()] = 0
            self.d[Set()] = []
            for ith in range(15):
                self.d[Set()].append(VarSet(ith))
                if m_test_str_set_bapa:
                    print('(declare-fun {} () (Set String))'.format(VarSet(ith)))
                else:
                    print('(declare-fun {} () (Set Int))'.format(VarSet(ith)))
                self.dict[Set()] += 1
            if m_test_set_eq and (not m_test_str_set_bapa):
                # if True:
                print("(declare-fun seteq ((Set Int) (Set Int)) Bool)")
                print(
                    "(assert (forall ((?s1 (Set Int)) (?s2 (Set Int))) (= (seteq ?s1 ?s2) (= ?s1 ?s2))))")
                print(
                    "(assert (forall ((?s1 (Set Int)) (?s2 (Set Int)))"
                    " (= (seteq ?s1 ?s2) (and (subset ?s1 ?s2) (subset ?s2 ?s1)))))")

        if m_test_bag_bapa:
            self.dict[Bag()] = 0
            self.d[Bag()] = []
            for ith in range(15):
                self.d[Bag()].append(VarBag(ith))
                print('(declare-fun {} () (Bag Int))'.format(VarBag(ith)))
                self.dict[Bag()] += 1

        if (m_test_string or m_test_string_lia) and (not m_test_datalog_chc):
            self.dict[String()] = 0
            self.d[String()] = []
            self.dict[Regular()] = 0
            self.d[Regular()] = []
            self.dict[Seq()] = 0
            self.d[Seq()] = []
            nstr = random.randint(5, 20)
            if m_test_seq:
                for ith in range(nstr):
                    self.d[Seq()].append(VarSeq(ith))
                    print('(declare-fun {} () (Seq Int))'.format(VarSeq(ith)))
                    self.dict[Seq()] += 1
                # return #TEMP: mixing seq and str

            for ith in range(nstr):
                self.d[String()].append(VarString(ith))
                print('(declare-fun {} () String)'.format(VarString(ith)))
                self.dict[String()] += 1

            if m_test_my_uf:
                print("(declare-fun ufss3 (String String String) String)")
                print("(declare-fun ufss4 (String String String String) String)")
                print("(declare-fun ufss5 (String String String String String) String)")
                print(
                    "(declare-fun ufss6 (String String String String String String) String)")
                print(
                    "(declare-fun ufss7 (String String String String String String String) String)")

                print("(declare-fun ufss3_2 (String String String) String)")
                print("(declare-fun ufss4_2 (String String String String) String)")
                print(
                    "(declare-fun ufss5_2 (String String String String String) String)")
                print(
                    "(declare-fun ufss6_2 (String String String String String String) String)")
                print(
                    "(declare-fun ufss7_2 (String String String String String String String) String)")

            # init someRE?
            # '''
            if m_test_string_re:
                for ith in range(15):
                    if random.random() < 0.65:
                        par = random.choice(self.d[String()])
                    else:
                        par = "\"" + random_string() + "\""
                    operands = str(par)
                    new_re = RegularOp('str.to_re', operands)
                    self.d[Regular()].append(new_re)

                    self.d[Regular()].append("re.allchar")
                    self.d[Regular()].append("re.all")
                    self.d[Regular()].append("re.none")

        if m_test_recfun:
            self.define_rec_fun()

    # TODO: maintain the "liveness" of named assertions when using push/pop

    def push(self, k=1):
        global m_all_assertions, m_backtrack_points

        print('(push ' + str(k) + ')')

        for ss in range(k):
            self.new_keys.append(len(list(self.d)))

            self.indices.append([])
            for key in self.d:
                self.indices[-1].append(len(self.d[key]))

            point = len(m_all_assertions)
            m_backtrack_points.append(point)

    def pop(self, k=1):
        global m_all_assertions, m_backtrack_points

        print('(pop ' + str(k) + ')')

        for ss in range(k):
            n_keys = self.new_keys[-1]
            self.new_keys.pop()
            added_keys = list(self.d)[n_keys:]
            for ones in added_keys:
                del self.d[ones]

            for key in self.d:
                jj = self.indices[-1][list(self.d).index(key)]
                del self.d[key][jj:]
            self.indices.pop()

            point = m_backtrack_points.pop()
            m_all_assertions = m_all_assertions[0:point]

    #
    def define_rec_fun(self):
        # return
        # Define recustive function
        # I will reuse qdict
        simp = SimpleNodes(['x', 'y'], "Int")
        term = simp.get_int_term()
        print("(define-fun recfun2 ((x Int) (y Int)) Int " + str(term) + ")")

        simp = SimpleNodes(['x', 'y', 'z'], "Int")
        term = simp.get_int_term()
        print("(define-fun recfun3 ((x Int) (y Int) (z Int)) Int " + str(term) + ")")

    # only for CHC
    def quantifier_chc(self):
        # TODO: choose the number of variales in each rule!!!!!!!
        # Not just 3
        # try m_test_datalog_chc_var_bound

        sorted_var = '('
        n = random.randint(0, m_test_datalog_chc_var_bound)
        for _ in range(n):
            ovar = VarQuant(self.nq)
            self.nq += 1
            # osort = random.choice(list(self.d))
            osort = None
            if m_test_datalog_chc_logic == "int":
                for o in list(self.d):
                    if isinstance(o, Int):
                        osort = o
                        break
            elif m_test_datalog_chc_logic == "real":
                for o in list(self.d):
                    if isinstance(o, Real):
                        osort = o
                        break
            elif m_test_datalog_chc_logic == "bv":
                for o in list(self.d):
                    if isinstance(o, BV):
                        osort = o
                        break

            if osort and (osort not in self.qdict):
                self.qdict[osort] = []
            self.qdict[osort].append(ovar)
            osv = '({} {}) '.format(ovar, osort)
            sorted_var += osv

        ovar = VarQuant(self.nq)
        self.nq += 1
        osort = random.choice(list(self.d))
        if osort not in self.qdict:
            self.qdict[osort] = []
        self.qdict[osort].append(ovar)
        osv = '({} {}))'.format(ovar, osort)
        sorted_var += osv

        # try more multile times?
        times_batch = 1  # how many assertions for a group of quantified vars.
        for _ in range(0, times_batch):
            stat, term = self.qterm_chc()
            # print("stat, term", stat, term)
            if stat:
                statement = '(assert (forall {} {}))'.format(sorted_var, term)
                print(statement)

        self.qdict.clear()

    def qterm_chc(self):
        qkeys = list(self.qdict)
        nsam = 2
        if len(qkeys) < 2:
            return False, "Error"
        qkeys = random.sample(qkeys, nsam)
        boolean_subexpressions = ""
        for ith in qkeys:
            subexpr = self.qsubexpression_chc(ith)
            boolean_subexpressions += (str(subexpr) + " ")
        boolean_subexpressions = boolean_subexpressions[:-1]
        if nsam == 2:  # binary
            term = '({} {})'.format(
                random.choice(BiOp),
                boolean_subexpressions)
            return True, term

    def quantifier(self):
        global m_assert_id, m_all_assertions
        sorted_var = '('
        var_list = []
        # n = random.randint(0, 3)
        n = random.randint(0, 7)
        for _ in range(n):
            ovar = VarQuant(self.nq)
            self.nq += 1
            osort = random.choice(list(self.d))
            if osort not in self.qdict:
                self.qdict[osort] = []
            self.qdict[osort].append(ovar)
            osv = '({} {}) '.format(ovar, osort)
            sorted_var += osv
            var_list.append(osv)
        ovar = VarQuant(self.nq)
        self.nq += 1
        osort = random.choice(list(self.d))
        if osort not in self.qdict:
            self.qdict[osort] = []
        self.qdict[osort].append(ovar)
        osv = '({} {}))'.format(ovar, osort)
        sorted_var += osv
        var_list.append('({} {})'.format(ovar, osort))

        term = self.qterm()

        if random.random() < 0.5:
            notqterm = random.random()
            if notqterm < 0.5:
                if random.random() < 0.45:
                    statement = '(forall {} {})'.format(sorted_var, term)
                else:
                    statement = '(exists {} {})'.format(sorted_var, term)

                self.d[Bool()].append(statement)
            else:
                if random.random() < 0.45:
                    statement = '(not (forall {} {}))'.format(sorted_var, term)
                else:
                    statement = '(not (exists {} {}))'.format(sorted_var, term)

                self.d[Bool()].append(statement)

        if not m_use_fancy_qterm:
            self.qdict.clear()
            return
        elif random.random() < 0.5:
            termone = self.qterm()
            termtwo = self.qterm()
            if random.random() < 0.25:  # experimetal: try forall exists randomly
                prex = ''
                for var in var_list:
                    if random.random() < 0.5:
                        prex = prex + ' (forall ({}) '.format(var)
                    else:
                        prex = prex + ' (exists ({}) '.format(var)

                fst = ' (' + random.choice(['or', 'xor',
                                            'and', 'or']) + ' {} '.format(termone)
                for _ in range(5):
                    tmp = random.choice(self.d[Bool()])
                    fst += ' {} '.format(tmp)

                new_bool = prex + fst + ')'
                for _ in var_list:
                    new_bool = new_bool + ')'

                self.d[Bool()].append(new_bool)
                self.qdict.clear()  # why clear?
                return

            # the orginal fancy
            stmtx = ' (forall {} {})'.format(sorted_var, termtwo)
            stmty = ' (exists {} {})'.format(sorted_var, termtwo)

            if random.random() < 0.5:
                fstt = '(forall {}'.format(sorted_var)
            else:
                fstt = '(exists {}'.format(sorted_var)

            # fstt += ' (or {} '.format(termone)  # should we?
            fstt += ' (' + random.choice(['or', 'xor',
                                          'and', 'or']) + ' {} '.format(termone)
            if random.random() < 0.5:
                fstt += stmtx
            else:
                fstt += stmty
            for _ in range(5):
                tmp = random.choice(self.d[Bool()])
                fstt += ' {} '.format(tmp)
            fstt += '))'
            new_bool = fstt
            if random.random() < 0.5:
                new_bool = '(not ' + fstt + ')'
            self.d[Bool()].append(new_bool)
            # print('(assert ' + fstt + ' )')

        self.qdict.clear()  # why clear?

    def qterm(self):
        qkeys = list(self.qdict)
        nsam = random.randint(0, len(self.qdict.keys()))
        qkeys = random.sample(qkeys, nsam)
        if nsam == 0:
            term = random.choice(self.d[Bool()])
            return term
        boolean_subexpressions = ""
        for ith in qkeys:
            subexpr = self.qsubexpression(ith)
            boolean_subexpressions += (str(subexpr) + " ")
        boolean_subexpressions = boolean_subexpressions[:-1]
        if nsam == 1:  # unary
            term = '({} {})'.format(
                random.choice(UnOp),
                boolean_subexpressions)
        elif nsam == 2:  # binary
            term = '({} {})'.format(
                random.choice(BiOp),
                boolean_subexpressions)
        else:  # n-array
            term = '({} {})'.format(
                random.choice(NarOp),
                boolean_subexpressions)

        return term

    def extend_qdict_array(self):
        # TOOD: too complex??...
        return None

    def extend_qdict_bv(self):
        options = []
        qkeys = list(self.qdict)
        for sort in qkeys:
            if isinstance(sort, BV):
                options.append(sort)

        if len(options) > 0:
            s = random.choice(options)
            prob = random.random()
            if prob < 0.05:  # concat
                s2 = random.choice(options)
                width = s.w + s2.w
                par1 = random.choice(self.qdict[s])
                par2 = random.choice(self.qdict[s2])
                operand = str(par1) + " " + str(par2)
                new_bv = BVOp("concat", operand)
                bv_sort = BV(width)
                if bv_sort not in qkeys:
                    self.qdict[bv_sort] = []
                self.qdict[bv_sort].append(new_bv)

            elif prob < 0.1 and (not m_test_eldarica):  # repeat
                ii = random.randint(1, 10)
                width = ii * s.w
                operator = '(_ repeat {})'.format(ii)
                par = random.choice(self.qdict[s])
                new_bv = BVOp(operator, par)
                bv_sort = BV(width)
                if bv_sort not in qkeys:
                    self.qdict[bv_sort] = []
                self.qdict[bv_sort].append(new_bv)

            elif prob < 0.2:  # unary, extract
                if random.random() < 0.5:  # unary
                    par = random.choice(self.qdict[s])
                    new_bv = BVOp(random.choice(Un_BV_BV), par)
                    self.qdict[s].append(new_bv)
                else:  # extract
                    width = s.w
                    parameter1 = random.randrange(0, width)
                    parameter2 = random.randint(0, parameter1)
                    operator = "(_ extract {} {})".format(
                        parameter1, parameter2)
                    new_width = parameter1 - parameter2 + 1
                    par = random.choice(self.qdict[s])
                    new_bv = BVOp(operator, par)
                    bv_sort = BV(new_width)
                    if bv_sort not in qkeys:
                        self.qdict[bv_sort] = []
                    self.qdict[bv_sort].append(new_bv)

            elif prob < 0.3:
                ii = random.randint(0, 10)
                if random.random() < 0.5:
                    if random.random() < 0.5:
                        operator = "(_ zero_extend {})".format(ii)
                    else:
                        operator = "(_ sign_extend {})".format(ii)
                    width = s.w + ii
                    par = random.choice(self.qdict[s])
                    new_bv = BVOp(operator, par)
                    bv_sort = BV(width)
                    if bv_sort not in qkeys:
                        self.qdict[bv_sort] = []
                    self.qdict[bv_sort].append(new_bv)
                elif not m_test_eldarica:  # for Eldarica CHC
                    if random.random() < 0.5:
                        operator = "(_ rotate_left {})".format(ii)
                    else:
                        operator = "(_ rotate_right {})".format(ii)
                    par = random.choice(self.qdict[s])
                    new_bv = BVOp(operator, par)
                    self.qdict[s].append(new_bv)

            elif prob < 0.4 and not m_test_eldarica:  # n-array
                a = random.randint(1, 3)
                par = random.choice(self.qdict[s])
                operand = str(par)
                for ii in range(a):
                    par = random.choice(self.qdict[s])
                    operand += (" " + str(par))
                new_bv = BVOp(random.choice(N_BV_BV), operand)
                self.qdict[s].append(new_bv)

            else:  # binary
                par1 = random.choice(self.qdict[s])
                par2 = random.choice(self.qdict[s])
                operand = str(par1) + " " + str(par2)
                operator = random.choice(Bin_BV_BV)
                new_bv = BVOp(operator, operand)
                if operator == "bvcomp":
                    if BV(1) not in qkeys:
                        self.qdict[BV(1)] = []
                    self.qdict[BV(1)].append(new_bv)
                else:
                    self.qdict[s].append(new_bv)

    def extend_qdict(self):
        # Make the qterm for CHC more fancy!!!!
        qkeys = list(self.qdict)

        # TODO: Sapcer only supports linear int, liner real, bv.
        # We need to filter non-linear terms of int and real!!!!!!!

        if m_test_datalog_chc_logic == 'int':
            for sort in qkeys:
                if isinstance(sort, Int):
                    # create some int numbers for use
                    # In fact, we already creat some in the "Nodes" class
                    for _ in range(0, 3):
                        new_int = random.randint(0, 1000)
                        self.qdict[sort].append(new_int)

                    p = random.random()
                    if p < 0.4:  # unary
                        par = random.choice(self.qdict[sort])
                        new_int = IntOp(random.choice(IntUnOp), par)
                        self.qdict[sort].append(new_int)
                    elif p < 0.65:  # binary
                        num_created = 0
                        for _ in range(
                                0, 10):  # try more times in case we meet many non-linear terms
                            int_op_use = random.choice(IntBinOp)
                            par1 = random.choice(self.qdict[sort])
                            operand = str(par1)
                            par2 = random.choice(self.qdict[sort])
                            if not m_test_datalog_chc_nonlinear and int_op_use in [
                                    "div", "*", "mod"]:
                                par2 = str(random.randint(1, 1000))
                            operand += (" " + str(par2))
                            new_int = IntOp(int_op_use, operand)
                            self.qdict[sort].append(new_int)
                            num_created += 1
                            if num_created == 4:
                                break
                    else:
                        num_created = 0
                        for _ in range(0, 10):
                            num_int_var = 0
                            par = random.choice(self.qdict[sort])
                            if 'q' in str(par):
                                num_int_var += 1
                            operand = str(par)
                            n = random.randrange(1, 5)
                            for _ in range(n):
                                par = random.choice(self.qdict[sort])
                                if 'q' in str(par):
                                    num_int_var += 1
                                operand += (" " + str(par))

                            op_to_use = random.choice(IntNOp)
                            # prevent non-linear
                            if not m_test_datalog_chc_nonlinear:
                                # if m_global_logic in lia_logics:
                                if op_to_use == "*" and num_int_var >= 2:
                                    continue

                            new_int = IntOp(op_to_use, operand)
                            self.qdict[sort].append(new_int)
                            num_created += 1
                            if num_created == 4:
                                break
                    break
        elif m_test_datalog_chc_logic == 'real':
            for sort in qkeys:
                if isinstance(sort, Real):
                    # create some real numbers for use
                    # In fact, we already creat some in the "Nodes" class
                    for _ in range(0, 3):
                        new_real = random_real()
                        self.qdict[sort].append(new_real)

                    chance = random.random()
                    if chance < 0.33:
                        par = random.choice(self.qdict[sort])
                        new_real = RealOp(
                            random.choice(RealUnOp), par)  # Op2 has sin/cos
                        self.qdict[sort].append(new_real)

                    elif chance < 0.66:  # binary
                        num_created = 0
                        for _ in range(0, 15):
                            real_op_use = random.choice(RealBinOp)
                            par1 = random.choice(self.qdict[sort])
                            operand = str(par1)
                            par2 = random.choice(self.qdict[sort])
                            if not m_test_datalog_chc_nonlinear:
                                par2 = random_real()
                            operand += (" " + str(par2))
                            new_real = RealOp(real_op_use, operand)
                            self.qdict[sort].append(new_real)
                            num_created += 1
                            if num_created == 4:
                                break

                    else:
                        num_created = 0
                        for _ in range(0, 5):
                            num_real_var = 0
                            par = random.choice(self.qdict[sort])
                            if 'q' in str(par):
                                num_real_var += 1
                            operand = str(par)
                            n = random.randrange(1, 5)
                            for _ in range(n):
                                par = random.choice(self.qdict[sort])
                                if 'q' in str(par):
                                    num_real_var += 1
                                operand += (" " + str(par))
                            op_to_use = random.choice(RealNOp)

                            # if not m_test_datalog_chc_nonlinear:
                            if m_global_logic in lra_logics:
                                if op_to_use == "*" and num_real_var >= 2:
                                    continue

                            new_real = RealOp(op_to_use, operand)
                            self.qdict[sort].append(new_real)
                            num_created += 1
                            if num_created == 4:
                                break
                    break
        # if 'BV' in m_global_logic: self.extend_qdict_bv()
        elif m_test_datalog_chc_logic == 'bv':
            for _ in range(0, 3):
                self.extend_qdict_bv()

    def qsubexpression_chc(self, sort):
        subexpr = "true"
        self.extend_qdict()  # corrent?

        if isinstance(sort, Bool):
            p = random.randint(1, 6)
            if p == 1:
                par = random.choice(self.qdict[sort])
                subexpr = BoolOp(random.choice(UnOp), par)
            elif p == 2:
                par1 = random.choice(self.qdict[sort])
                par2 = random.choice(self.qdict[sort])
                operand = str(par1)
                operand += (" " + str(par2))
                subexpr = BoolOp(random.choice(BiOp), operand)
            else:
                n_operands = random.randint(1, 8)
                par = random.choice(self.qdict[sort])
                operands = str(par)
                for _ in range(n_operands):
                    par = random.choice(self.qdict[sort])
                    operands += (" " + str(par))
                subexpr = BoolOp(random.choice(NarOp), operands)
                # TODO: Can use fancy Boolean for CHC??
                # do we need the following restriction?
                # if m_test_datalog_chc:
                #    subexpr = Bool_Op("and", operands)

        if isinstance(sort, Int):
            '''
            par = random.choice(self.qdict[sort])
            operand = str(par)
            par = random.choice(self.qdict[sort])
            operand += (" " + str(par))
            subexpr = Bool_Op(random.choice(IRNBoolOp), operand)
            '''
            par = random.choice(self.qdict[sort])
            operands = str(par)
            n_operands = random.randrange(1, 4)
            for _ in range(n_operands):
                par = random.choice(self.qdict[sort])
                operands += (" " + str(par))
            subexpr = BoolOp(random.choice(IRNBoolOp), operands)

        if isinstance(sort, Real):
            par = random.choice(self.qdict[sort])
            operands = str(par)
            n_operands = random.randrange(1, 4)
            for _ in range(n_operands):
                par = random.choice(self.qdict[sort])
                operands += (" " + str(par))
            subexpr = BoolOp(random.choice(IRNBoolOp), operands)

        if isinstance(sort, BV):
            if random.random() < 0.33:
                par1 = random.choice(self.qdict[sort])
                par2 = random.choice(self.qdict[sort])
                operand = str(par1) + " " + str(par2)
                subexpr = BoolOp(random.choice(Bin_BV_Bool), operand)
            else:
                par = random.choice(self.qdict[sort])
                operand = str(par)
                # n = random.randint(1, 4)
                par = random.choice(self.qdict[sort])
                operand += (" " + str(par))
                subexpr = BoolOp(random.choice(N_BV_Bool), operand)

        if isinstance(sort, Arr):
            isort = sort.sort_index
            if isort in self.d.keys() and len(self.d[sort.sort_index]) > 0:
                par = random.choice(self.qdict[sort])

                par2 = "Empty"
                if sort in self.qdict and len(self.qdict[isort]) > 0:
                    par2 = random.choice(self.qdict[isort])

                if par2 != "Empty":
                    expression = '{} {}'.format(par, par2)
                    subexpr = BoolOp('select', expression)
            else:
                par = random.choice(self.qdict[sort])
                operand = str(par)
                n = random.randint(1, 4)
                for _ in range(n):
                    par = random.choice(self.qdict[sort])
                    operand += (" " + str(par))
                if random.random() < 0.5:
                    subexpr = BoolOp('=', operand)
                else:
                    subexpr = BoolOp('distinct', operand)
        # if subexpr != None:
        return subexpr

    def qsubexpression(self, sort):
        subexpr = "true"
        # NOTE: extend_qdict is previously used for CHC.
        # not sure if it works for benera qterms
        # self.extend_qdict() # correct??

        if isinstance(sort, Bool):
            p = random.randint(1, 7)
            if p == 1:
                if random.random() < 0.5:
                    par = random.choice(self.qdict[sort])
                else:
                    par = random.choice(self.d[Bool()])
                subexpr = BoolOp(random.choice(UnOp), par)
            elif p == 2:
                if random.random() < 0.5:
                    par1 = random.choice(self.qdict[sort])
                else:
                    par1 = random.choice(self.d[Bool()])
                if random.random() < 0.5:
                    par2 = random.choice(self.qdict[sort])
                else:
                    par2 = random.choice(self.d[Bool()])
                operand = str(par1)
                operand += (" " + str(par2))
                subexpr = BoolOp(random.choice(BiOp), operand)
            else:
                n_operands = random.randint(1, 10)
                if random.random() < 0.5:
                    par = random.choice(self.qdict[sort])
                else:
                    par = random.choice(self.d[Bool()])
                operands = str(par)
                for _ in range(n_operands):
                    if random.random() < 0.5:
                        par = random.choice(self.qdict[sort])
                    else:
                        par = random.choice(self.d[Bool()])

                    operands += (" " + str(par))

                op_to_use = random.choice(NarOp)
                subexpr = BoolOp(op_to_use, operands)

        if isinstance(sort, Int):
            if random.random() < 0.5:
                par = random.choice(self.d[Int()])
            else:
                par = random.choice(self.qdict[sort])
            operand = str(par)
            if random.random() < 0.5:
                par = random.choice(self.d[Int()])
            else:
                par = random.choice(self.qdict[sort])
            operand += (" " + str(par))
            subexpr = BoolOp(random.choice(IRNBoolOp), operand)

        if isinstance(sort, Real):
            if random.random() < 0.5:
                par = random.choice(self.d[Real()])
            else:
                par = random.choice(self.qdict[sort])
            operands = str(par)
            n_operands = random.randrange(1, 5)
            for _ in range(n_operands):
                if random.random() < 0.5:
                    par = random.choice(self.d[Real()])
                else:
                    par = random.choice(self.qdict[sort])
                operands += (" " + str(par))
            subexpr = BoolOp(random.choice(IRNBoolOp), operands)

        if isinstance(sort, FP):
            if random.random() < 0.5:
                par = random.choice(self.d[FP()])
            else:
                par = random.choice(self.qdict[sort])
            operands = str(par)
            n_operands = random.randrange(1, 5)
            for _ in range(n_operands):
                if random.random() < 0.5:
                    par = random.choice(self.d[FP()])
                else:
                    par = random.choice(self.qdict[sort])
                operands += (" " + str(par))
            subexpr = BoolOp(random.choice(IRNFPBoolOp), operands)

        if isinstance(sort, BV):
            if random.random() < 0.33:
                if random.random() < 0.5 and len(self.d[sort]) > 0:
                    par1 = random.choice(self.d[sort])
                else:
                    par1 = random.choice(self.qdict[sort])
                if random.random() < 0.5 and len(self.d[sort]) > 0:
                    par2 = random.choice(self.d[sort])
                else:
                    par2 = random.choice(self.qdict[sort])
                operand = str(par1) + " " + str(par2)
                subexpr = BoolOp(random.choice(Bin_BV_Bool), operand)
            else:
                if random.random() < 0.5 and len(self.d[sort]) > 0:
                    par = random.choice(self.d[sort])
                else:
                    par = random.choice(self.qdict[sort])
                operand = str(par)
                n = random.randint(1, 4)
                for _ in range(n):
                    if random.random() < 0.5 and len(self.d[sort]) > 0:
                        par = random.choice(self.d[sort])
                    else:
                        par = random.choice(self.qdict[sort])
                    operand += (" " + str(par))
                subexpr = BoolOp(random.choice(N_BV_Bool), operand)

        if isinstance(sort, Arr):
            # TODO: do we need the following restrictions for bv logics???
            # (need test)
            no_fancy_array_logics = [
                'ANIA',
                'ALIA',
                'AUFNIA',
                'AUFLIA',
                'ALL',
                'AX',
                'QF_AX',
                'ABV',
                'AUFBV',
                'ANRA',
                'AUFNRA',
                'ALRA',
                'AUFLRA',
                'ALIRA',
                'ANIRA',
                'AUFLIRA',
                'AUFNIRA']
            if m_global_logic in no_fancy_array_logics:
                isort = sort.sort_index
                # TODO:!!!!!!!! This is a  didty fix for the above logics, whcich disables "select" in qterm totally.
                # At least, we know where the issus is from: select
                par = random.choice(self.qdict[sort])
                operand = str(par)
                n = random.randint(1, 4)
                for _ in range(n):
                    par = random.choice(self.qdict[sort])
                    operand += (" " + str(par))
                if random.random() < 0.5:
                    subexpr = BoolOp('=', operand)
                else:
                    subexpr = BoolOp('distinct', operand)

                return subexpr

            isort = sort.sort_index
            if random.random() < 0.5 and isort in self.d.keys() and len(
                    self.d[sort.sort_index]) > 0:
                if random.random() < 0.5 and len(self.d[sort]) > 0:
                    par = random.choice(self.d[sort])
                else:
                    par = random.choice(self.qdict[sort])
                if random.random() < 0.5 and isort in self.qdict and len(
                        self.qdict[isort]) > 0:
                    par2 = random.choice(self.qdict[isort])
                else:
                    par2 = random.choice(self.d[isort])
                expression = '{} {}'.format(par, par2)
                subexpr = BoolOp('select', expression)
            else:
                if random.random() < 0.5 and len(self.d[sort]) > 0:
                    par = random.choice(self.d[sort])
                else:
                    par = random.choice(self.qdict[sort])
                operand = str(par)
                n = random.randint(1, 4)
                for _ in range(n):
                    if random.random() < 0.5 and len(self.d[sort]) > 0:
                        par = random.choice(self.d[sort])
                    else:
                        par = random.choice(self.qdict[sort])
                    operand += (" " + str(par))
                if random.random() < 0.5:
                    subexpr = BoolOp('=', operand)
                else:
                    subexpr = BoolOp('distinct', operand)

        if isinstance(sort, UnIntSort):
            n_items = random.randrange(1, 5)
            if random.random() < 0.5 and len(self.d[sort]) > 0:
                par = random.choice(self.d[sort])
            else:
                par = random.choice(self.qdict[sort])
            items = str(par)
            for _ in range(n_items):
                if random.random() < 0.5 and len(self.d[sort]) > 0:
                    par = random.choice(self.d[sort])
                else:
                    par = random.choice(self.qdict[sort])
                items += (" " + str(par))
            if random.random() < 0.5:
                subexpr = BoolOp('=', items)
            else:
                subexpr = BoolOp('distinct', items)

                # if subexpr != None:
        return subexpr

    def newSort(self):
        n_unintsorts = 0
        for o in list(self.d):
            if isinstance(o, UnIntSort):
                n_unintsorts += 1
        if n_unintsorts < 5:
            current_sort = UnIntSort(n_unintsorts)
            print('(declare-sort {} 0)'.format(current_sort))
            self.d[current_sort] = []
            self.dict[current_sort] = 0
        else:
            pass

    def varUSort(self):
        options = []
        for o in list(self.d):
            if isinstance(o, UnIntSort):
                options.append(o)
        if len(options) > 0:
            current_sort = random.choice(options)
            n = len(self.d[current_sort])
            self.d[current_sort].append(VarUnIntSort(current_sort, n))
            print(
                '(declare-fun {} () {})'.format(VarUnIntSort(current_sort, n), current_sort))
            self.dict[current_sort] += 1

    def bool_from_usort(self):
        ops = []
        options = []
        for o in list(self.d):
            if isinstance(o, UnIntSort):
                ops.append(o)
        for things in ops:
            if len(self.d[things]) > 0:
                options.append(things)
        if len(options) > 0:
            current_sort = random.choice(options)
            n_items = random.randrange(1, 5)
            par = random.choice(self.d[current_sort])
            items = str(par)
            for _ in range(n_items):
                par = random.choice(self.d[current_sort])
                items += (" " + str(par))
            if random.random() < 0.5:
                new_bool = BoolOp('=', items)
            else:
                new_bool = BoolOp('distinct', items)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1

            if m_test_ufc:  # and random.random() < 0.5:
                current_sort = random.choice(options)
                par = random.choice(self.d[current_sort])
                # if random.random() < 0.5:
                print('(assert (fmf.card ' + str(par) + ' ' +
                      str(random.randint(1, 100)) + ' ))')
                # else: print('(assert (not (fmf.card ' + str(par) + ' 2)))')

    def new_bool(self):
        new_var = VarBool(self.n_vars)
        print('(declare-fun {} () Bool)'.format(new_var))
        self.n_vars += 1
        self.d[Bool()].append(new_var)
        self.dict[Bool()] += 1

    def new_int(self):
        if random.random() < 0.3:
            new_int = VarInt(self.n_ints)
            print('(declare-fun {} () Int)'.format(new_int))
            self.n_ints += 1
            self.d[Int()].append(new_int)
        else:
            new_int = random.randint(0, 1000)
            self.d[Int()].append(str(new_int))
        self.dict[Int()] += 1

        if m_test_my_uf and random.random() < 0.1:
            par = random.choice(self.d[Int()])
            operands = str(par)
            n_operands = random.randrange(2, 7)
            for _ in range(n_operands):
                par = random.choice(self.d[Int()])
                operands += (" " + str(par))
            new_int = random.randint(0, 1000)
            new_int2 = new_int
            if n_operands == 2:
                if random.random() < 0.5:
                    new_int2 = IntOp('ufii3', operands)
                else:
                    new_int2 = IntOp('ufii3_2', operands)
            elif n_operands == 3:
                if random.random() < 0.5:
                    new_int2 = IntOp('ufii4', operands)
                else:
                    new_int2 = IntOp('ufii4_2', operands)
            elif n_operands == 4:
                if random.random() < 0.5:
                    new_int2 = IntOp('ufii5', operands)
                else:
                    new_int2 = IntOp('ufii5_2', operands)
            elif n_operands == 5:
                if random.random() < 0.5:
                    new_int2 = IntOp('ufii6', operands)
                else:
                    new_int2 = IntOp('ufii6_2', operands)
            elif n_operands == 6:
                if random.random() < 0.5:
                    new_int2 = IntOp('ufii7', operands)
                else:
                    new_int2 = IntOp('ufii7_2', operands)

            par = random.choice(self.d[Bool()])
            operands = str(par)
            n_operands = random.randrange(2, 7)
            for _ in range(n_operands):
                par = random.choice(self.d[Bool()])
                operands += (" " + str(par))
            new_b = random.choice(self.d[Int()])
            if n_operands == 2:
                new_b = IntOp('ufbi3', operands)
            elif n_operands == 3:
                new_b = IntOp('ufbi4', operands)
            elif n_operands == 4:
                new_b = IntOp('ufbi5', operands)
            elif n_operands == 5:
                new_b = IntOp('ufbi6', operands)
            elif n_operands == 6:
                new_b = IntOp('ufbi7', operands)

            if random.random() < 0.5:
                self.d[Int()].append(new_int2)
            else:
                self.d[Int()].append(new_b)

    def int_from_int(self):
        if m_test_iand:
            par1 = random.choice(self.d[Int()])
            par2 = random.choice(self.d[Int()])
            width = "4"
            if random.random() < 0.5:
                width = "8"
            # (assert (> ((_ iand 4) x y) 0))
            new_int = "((_ iand {}) {} {})".format(width, par1, par2)
            self.d[Int()].append(new_int)

        if m_test_bvint and random.random() < 0.5:
            options = []
            for o in list(self.d):
                if isinstance(o, BV):
                    options.append(o)
            if len(options) > 0:
                s = random.choice(options)
                bv = random.choice(self.d[s])
                new_int = "(bv2nat {})".format(bv)
                self.d[Int()].append(new_int)

        if m_test_recfun and random.random() < 0.1:
            par1 = random.choice(self.d[Int()])
            par2 = random.choice(self.d[Int()])
            par3 = random.choice(self.d[Int()])
            new_int = "(recfun2 {} {})".format(par1, par2)
            if random.random() < 0.5:
                new_int = "(recfun3 {} {} {})".format(par1, par2, par3)
            self.d[Int()].append(new_int)

        if m_global_logic == 'QF_IDL' or m_global_logic == 'IDL' or m_global_logic == 'QF_UFIDL':
            # if random.random() < 0.25:
            parone = random.choice(self.d[Int()])
            operands = str(parone)
            partwo = random.choice(self.d[Int()])
            operands += (" " + str(partwo))
            self.d[Int()].append(IntOp("-", operands))  # RDL
            return

        p = random.random()
        if p < 0.3:
            par = random.choice(self.d[Int()])
            new_int = IntOp(random.choice(IntUnOp), par)
            self.d[Int()].append(new_int)
        elif p < 0.66:
            try_times = 1
            if m_global_logic in lia_logics:
                try_times = 8
            for _ in range(try_times):
                num_int_var = 0
                par = random.choice(self.d[Int()])
                if 'i' in str(par) or 'uf' in str(par):
                    num_int_var += 1
                operand = str(par)
                n = random.randrange(1, 5)
                for _ in range(n):
                    par = random.choice(self.d[Int()])
                    if 'i' in str(par) or 'to' in str(par) or 'uf' in str(
                            par) or 'ca' in str(par) or 'le' in str(par):
                        num_int_var += 1
                    operand += (" " + str(par))

                op_to_use = random.choice(IntNOp)
                if m_global_logic in lia_logics:
                    if (op_to_use == "*" or op_to_use ==
                            "mod" or op_to_use == "div") and num_int_var >= 2:
                        continue
                    else:
                        new_int = IntOp(op_to_use, operand)
                        self.d[Int()].append(new_int)
                        break
                else:
                    new_int = IntOp(op_to_use, operand)
                    self.d[Int()].append(new_int)
                    break
        else:
            try_times = 1
            if m_global_logic in lia_logics:
                try_times = 8
            for _ in range(try_times):
                num_int_var = 0
                par = random.choice(self.d[Int()])
                if 'i' in str(par) or 'uf' in str(par) or 'le' in str(par):
                    num_int_var += 1
                operand = str(par)
                n = random.randrange(1, 5)
                for _ in range(n):
                    par = random.choice(self.d[Int()])
                    if 'i' in str(par) or 'uf' in str(par):
                        num_int_var += 1
                    operand += (" " + str(par))

                op_to_use = random.choice(IntNOp)
                if m_global_logic in lia_logics:
                    if (op_to_use == "*" or op_to_use ==
                            "mod" or op_to_use == "div") and num_int_var >= 2:
                        continue
                    else:
                        new_int = IntOp(op_to_use, operand)
                        self.d[Int()].append(new_int)
                        break
                else:
                    new_int = IntOp(op_to_use, operand)
                    self.d[Int()].append(new_int)
        self.dict[Int()] += 1

        if m_use_ite and random.random() < 0.05:
            parb = random.choice(self.d[Bool()])
            operand = str(parb)
            par1 = random.choice(self.d[Int()])
            operand += (" " + str(par1))
            par2 = random.choice(self.d[Int()])
            operand += (" " + str(par2))
            new_int = IteOp('ite', operand)
            self.d[Int()].append(new_int)

    def set_from_set(self):
        chance = random.random()
        if chance < 0.15:  # unary
            par = random.choice(self.d[Set()])
            new_set = SetOp(random.choice(SetUnOp), par)
            self.d[Set()].append(new_set)
        else:
            par = random.choice(self.d[Set()])
            operands = str(par)
            par = random.choice(self.d[Set()])
            operands += (" " + str(par))
            new_set = SetOp(random.choice(SetBinOp), operands)
            self.d[Set()].append(new_set)

        if m_use_ite and random.random() < 0.05:
            parb = random.choice(self.d[Bool()])
            operand = str(parb)
            par1 = random.choice(self.d[Set()])
            operand += (" " + str(par1))
            par2 = random.choice(self.d[Set()])
            operand += (" " + str(par2))
            new_set = IteOp('ite', operand)
            self.d[Set()].append(new_set)

    def bag_from_bag(self):
        chance = random.random()
        if chance < 0:  # unary
            par = random.choice(self.d[Bag()])
            new_bag = BagOp(random.choice(BagUnOp), par)
            self.d[Bag()].append(new_bag)
        else:
            par = random.choice(self.d[Bag()])
            operands = str(par)
            par = random.choice(self.d[Bag()])
            operands += (" " + str(par))
            new_bag = BagOp(random.choice(BagBinOp), operands)
            self.d[Bag()].append(new_bag)

    def seq_from_seq(self):
        global StringNOp
        chance = random.random()
        if chance < 0.45:
            par = random.choice(self.d[Int()])
            operands = str(par)
            new_str = SeqOp('seq.unit', operands)
            self.d[Seq()].append(new_str)
        elif chance < 0.75:
            par = random.choice(self.d[Seq()])
            operands = str(par)
            par = random.choice(self.d[Seq()])
            operands += (" " + str(par))
            new_str = SeqOp('seq.++', operands)
            self.d[Seq()].append(new_str)
        else:
            par = random.choice(self.d[Seq()])
            operands = str(par)
            operands += (" " + str(random.choice(self.d[Int()])))
            operands += (" " + str(random.choice(self.d[Int()])))
            new_str = SeqOp('seq.extract', operands)
            self.d[Seq()].append(new_str)

    def bool_from_seq(self):
        global m_assert_id, m_all_assertions
        chance = random.random()
        if chance < 0.3 and m_test_string_lia:  # binary
            st = random.choice(self.d[Seq()])
            self.d[Int()].append(IntOp("seq.len", st))
        else:
            par = random.choice(self.d[Seq()])
            operands = str(par)
            par = random.choice(self.d[Seq()])
            operands += (" " + str(par))
            seqb = random.choice(
                ['seq.contains', 'seq.suffixof', 'seq.prefixof'])
            new_bool = SeqOp(seqb, operands)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1

    def string_from_string(self):
        global StringNOp
        if m_test_seq:
            self.seq_from_seq()
            if random.random() < 0.5:
                return

        chance = random.random()
        if chance < 0.1:  # unary
            new_str = "\"" + random_string() + "\""
            if random.random() < 0.35:
                par = random.choice(self.d[String()])
                operands = str(par)
                new_str = StringOp('str.rev', operands)
            self.d[String()].append(new_str)
        elif chance < 0.45:  # binary
            par = random.choice(self.d[String()])
            operands = str(par)
            par = random.choice(self.d[String()])
            operands += (" " + str(par))
            new_str = StringOp(random.choice(StringBinOp), operands)
            self.d[String()].append(new_str)
        else:
            par = random.choice(self.d[String()])
            operands = str(par)
            n = random.randrange(1, 5)
            for _ in range(n):
                if random.random() < 0.67:
                    par = random.choice(self.d[String()])
                    operands += (" " + str(par))
                else:
                    if m_test_string:
                        substr = random_string()
                        operands += (" " + "\"" + substr + "\"")
                    else:  # only works for m_test_string_lia
                        if random.random() < 0.22:
                            substr = random_string()
                            operands += (" " + "\"" + substr + "\"")
                        else:
                            if random.random() < 0.33:
                                if random.random() < 0.5:
                                    intstr = random.choice(self.d[String()])
                                    tmp_operands = str(intstr)
                                    new_int = IntOp("str.to_int", tmp_operands)
                                    self.d[Int()].append(new_int)
                                else:
                                    tmp_s1 = random.choice(self.d[String()])
                                    tmp_operands = str(tmp_s1)
                                    tmp_s2 = random.choice(self.d[String()])
                                    tmp_operands += (" " + str(tmp_s2))
                                    tmp_int = random.choice(self.d[Int()])
                                    tmp_operands += (" " + str(tmp_int))
                                    new_int = IntOp(
                                        "str.indexof", tmp_operands)
                                    self.d[Int()].append(new_int)

                            if random.random() < 0.22:
                                tmp_int = random.choice(self.d[Int()])
                                operands += (" (str.from_int " +
                                             str(tmp_int) + ")")
                            else:
                                tmp_str = random.choice(self.d[String()])
                                operands += (" " + str(tmp_str))

            if n == 2 and m_test_string_replace:
                StringNOp.append('str.replace_all')
                StringNOp.append('str.replace')
            op_to_use = random.choice(StringNOp)
            new_str = StringOp(op_to_use, operands)
            self.d[String()].append(new_str)
            StringNOp = ['str.++']
        # str.substr: (I add a global flag to control this)
        if m_test_string_lia and m_test_string_substr:
            par = random.choice(self.d[String()])
            operands = str(par)
            operands += (" " + str(random.choice(self.d[Int()])))
            if random.random() < 0.5:
                intstr = random.choice(self.d[String()])
                intv = " (str.to_int " + str(intstr) + ")"
                operands += (" " + str(intv))
            else:
                operands += (" " + str(random.choice(self.d[Int()])))
            new_str = StringOp('str.substr', operands)
            self.d[String()].append(new_str)
        if m_use_ite and random.random() < 0.05:
            parb = random.choice(self.d[Bool()])
            operand = str(parb)
            par1 = random.choice(self.d[String()])
            operand += (" " + str(par1))
            par2 = random.choice(self.d[String()])
            operand += (" " + str(par2))
            new_str = IteOp('ite', operand)
            self.d[String()].append(new_str)

        if m_test_string_re:
            reop = random.random()
            if reop < 0.35:
                rea = random.choice(self.d[Regular()])
                operands = str(rea)
                new_re = RegularOp(random.choice(ReUnOp), operands)
                self.d[Regular()].append(new_re)
            elif reop < 0.65:
                par = random.choice(self.d[Regular()])
                operands = str(par)
                n = random.randrange(1, 4)
                for _ in range(n):
                    par = random.choice(self.d[Regular()])
                    operands += (" " + str(par))
                op_to_use = random.choice(ReBinOp)
                new_re = RegularOp(op_to_use, operands)
                self.d[Regular()].append(new_re)
            else:
                str1 = random.choice(self.d[String()])
                str2 = random.choice(self.d[String()])
                re = random.choice(self.d[Regular()])
                if random.random() < 0.5:
                    new_str = "(str.replace_re_all {} {} {})".format(
                        str1, re, str2)
                else:
                    new_str = "(str.replace_re {} {} {})".format(
                        str1, re, str2)
                self.d[String()].append(new_str)

            if m_test_string_lia and False:
                # ((_ re.^ 5) (str.to_re "a"))
                i1 = random.choice(self.d[Int()])
                i2 = random.choice(self.d[Int()])
                re = random.choice(self.d[Regular()])
                new_re = "((_ re.loop {} {}) {})".format(i1, i2, re)
                self.d[Regular()].append(new_re)

        if m_test_my_uf and random.random() < 0.1:
            par = random.choice(self.d[String()])
            operands = str(par)
            n_operands = random.randrange(2, 7)
            for _ in range(n_operands):
                par = random.choice(self.d[String()])
                operands += (" " + str(par))
            new_int2 = par
            if n_operands == 2:
                if random.random() < 0.5:
                    new_int2 = RealOp('ufss3', operands)
                else:
                    new_int2 = RealOp('ufss3_2', operands)
            elif n_operands == 3:
                if random.random() < 0.5:
                    new_int2 = RealOp('ufss4', operands)
                else:
                    new_int2 = RealOp('ufss4_2', operands)
            elif n_operands == 4:
                if random.random() < 0.5:
                    new_int2 = RealOp('ufss5', operands)
                else:
                    new_int2 = RealOp('ufss5_2', operands)
            elif n_operands == 5:
                if random.random() < 0.5:
                    new_int2 = RealOp('ufss6', operands)
                else:
                    new_int2 = RealOp('ufss6_2', operands)
            elif n_operands == 6:
                if random.random() < 0.5:
                    new_int2 = RealOp('ufss7', operands)
                else:
                    new_int2 = RealOp('ufss7_2', operands)
            self.d[String()].append(new_int2)

    def bool_from_int(self):
        # can you choose multiple operands? chainable?
        if random.random() < 0.66:  # seems the old strategy is "better"?
            par = random.choice(self.d[Int()])
            operand = str(par)
            par = random.choice(self.d[Int()])
            operand += (" " + str(par))
            new_bool = BoolOp(random.choice(IRNBoolOp), operand)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1
            return  # stop here
        # else

        # n-array or binary?
        par = random.choice(self.d[Int()])
        operands = str(par)
        n_operands = random.randrange(1, 6)
        if "IDL" in m_global_logic:
            n_operands = 1  # Is this correct for enforcing IDL?
        for _ in range(n_operands):
            par = random.choice(self.d[Int()])
            operands += (" " + str(par))
        new_bool = BoolOp(random.choice(IRNBoolOp), operands)
        if m_test_my_uf and random.random() < 0.1:
            if n_operands == 2:
                new_bool = BoolOp('ufib3', operands)
            elif n_operands == 3:
                new_bool = BoolOp('ufib4', operands)
            elif n_operands == 4:
                new_bool = BoolOp('ufib5', operands)
            elif n_operands == 5:
                new_bool = BoolOp('ufib6', operands)
            elif n_operands == 6:
                new_bool = BoolOp('ufib7', operands)

        self.d[Bool()].append(new_bool)
        # give possibility of asserting this new bool here?
        self.dict[Bool()] += 1

    def bool_from_set(self):
        global IRNSetBoolOp
        if m_test_set_eq and (not m_test_str_set_bapa):
            IRNSetBoolOp = ["seteq", "subset", "subset", "subset"]
        par1 = random.choice(self.d[Set()])
        operands = str(par1)
        par2 = random.choice(self.d[Set()])
        operands += (" " + str(par2))
        bool_op_use = random.choice(IRNSetBoolOp)
        new_bool = BoolOp(bool_op_use, operands)
        self.d[Bool()].append(new_bool)
        IRNSetBoolOp = ["subset"]

    def bool_from_bag(self):
        set_pred = random.random()
        if set_pred < 0.7:
            par1 = random.choice(self.d[Bag()])
            operands = str(par1)
            par2 = random.choice(self.d[Bag()])
            operands += (" " + str(par2))
            bool_op_use = random.choice(IRNBagBoolOp)
            new_bool = BoolOp(bool_op_use, operands)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1
        elif set_pred < 0.8:
            par1 = random.choice(self.d[Bag()])
            operands = str(par1)
            bool_op_use = 'bag.is_singleton'
            new_bool = BoolOp(bool_op_use, operands)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1
        elif True:
            st = random.choice(self.d[Bag()])
            sz = random.choice(self.d[Int()])
            if random.random() < 0.5:
                print("(assert (> (bag.card " + str(st) + ") " + str(sz) + "))")
            else:
                print("(assert (< (bag.card " + str(st) + ") " + str(sz) + "))")

    def bool_from_seplog(self):
        if m_test_seplog:
            # pto: points-to
            if random.random() < 0.5:
                par = random.choice(self.d[Int()])
                operand = str(par)
                par = random.choice(self.d[Int()])
                operand += (" " + str(par))
                new_bool = BoolOp(random.choice(SeplogBinOp), operand)
                self.d[Bool()].append(new_bool)
                self.dict[Bool()] += 1
            else:
                par1 = random.choice(self.d[Bool()])
                par2 = random.choice(self.d[Bool()])
                operand = str(par1)
                operand += (" " + str(par2))
                new_bool = BoolOp(random.choice(SeplogNBoolOp), operand)
                self.d[Bool()].append(new_bool)

    def bool_from_string(self):
        global m_assert_id, m_all_assertions
        if m_test_seq:
            self.bool_from_seq()
            if random.random() < 0.5:
                return

        chance = random.random()
        # TODO:more unary
        if chance < 0.3 and m_test_string_lia:  # binary
            st = random.choice(self.d[String()])
            self.d[Int()].append(IntOp("str.len", st))
        elif chance < 0.5:
            par = random.choice(self.d[String()])
            operands = str(par)
            par = random.choice(self.d[String()])
            operands += (" " + str(par))
            new_bool = BoolOp(random.choice(StringBinBoolOp), operands)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1
        else:
            par = random.choice(self.d[String()])
            operands = str(par)
            op_to_use = random.choice(StringNBoolOp)
            n = random.randrange(1, 5)
            for _ in range(n):
                if random.random() < 0.9:
                    par = random.choice(self.d[String()])
                    operands += (" " + str(par))
                else:
                    if op_to_use == "distinct":
                        substr = random_string()
                        operands += (" " + "\"" + substr + "\"")
                    else:
                        par = random.choice(self.d[String()])
                        operands += (" " + str(par))

            new_bool = BoolOp(op_to_use, operands)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1

        if m_test_string_re and random.random() < 0.33:
            par = random.choice(self.d[String()])
            # para = random.choice(self.d[String()])
            # parb = random_string()
            cmd_b = "(str.in_re " + str(par)
            cmd_b += (" " + str(random.choice(self.d[Regular()]))) + ')'
            self.d[Bool()].append(cmd_b)

    def new_real(self):
        if random.random() < 0.5:
            self.d[Real()].append(VarReal(self.n_reals))
            print('(declare-fun {} () Real)'.format(VarReal(self.n_reals)))
            self.n_reals += 1
        else:
            new_real = random_real()
            self.d[Real()].append(new_real)
        self.dict[Real()] += 1

        if m_test_my_uf and random.random() < 0.1:
            par = random.choice(self.d[Real()])
            operands = str(par)
            n_operands = random.randrange(2, 7)
            for _ in range(n_operands):
                par = random.choice(self.d[Real()])
                operands += (" " + str(par))
            new_real = random_real()
            new_int2 = new_real
            if n_operands == 2:
                new_int2 = RealOp('ufrr3', operands)
            elif n_operands == 3:
                new_int2 = RealOp('ufrr4', operands)
            elif n_operands == 4:
                new_int2 = RealOp('ufrr5', operands)
            elif n_operands == 5:
                new_int2 = RealOp('ufrr6', operands)
            elif n_operands == 6:
                new_int2 = RealOp('ufrr7', operands)
            # self.d[Real()].append(new_int2)
            par = random.choice(self.d[Bool()])
            operands = str(par)
            n_operands = random.randrange(2, 7)
            for _ in range(n_operands):
                par = random.choice(self.d[Bool()])
                operands += (" " + str(par))
            new_b = random.choice(self.d[Real()])
            if n_operands == 2:
                new_b = IntOp('ufbr3', operands)
            elif n_operands == 3:
                new_b = IntOp('ufbr4', operands)
            elif n_operands == 4:
                new_b = IntOp('ufbr5', operands)
            elif n_operands == 5:
                new_b = IntOp('ufbr6', operands)
            elif n_operands == 6:
                new_b = IntOp('ufbr7', operands)

            if random.random() < 0.5:
                self.d[Real()].append(new_int2)
            else:
                self.d[Real()].append(new_b)

    def new_fp(self):
        if not m_test_fp_no_num and random.random() < 0.4:
            new_fp = random_fp()
            self.d[FP()].append(new_fp)
            self.dict[FP()] += 1
        else:
            self.d[FP()].append(VarFP(self.n_fps))
            if m_test_fp64:
                print('(declare-fun {} () Float64)'.format(VarFP(self.n_fps)))
            else:
                print('(declare-fun {} () Float32)'.format(VarFP(self.n_fps)))
            self.n_fps += 1
            self.dict[FP()] += 1

    def real_from_real(self):
        # lra_logics = ['QF_AUFLIRA', 'AUFLIRA', 'QF_RDL', 'QF_UFRDL', 'RDL',
        # 'QF_FPLRA', 'LRA', 'QF_LRA', 'UFLRA', 'QF_UFLRA', 'AUFLRA', 'QF_AUFLRA']

        if "RDL" in m_global_logic:
            if True:
                parone = random.choice(self.d[Real()])
                operands = str(parone)
                partwo = random.choice(self.d[Real()])
                operands += (" " + str(partwo))
                self.d[Real()].append(RealOp("-", operands))  # RDL
            return

        chance = random.random()
        if chance < 0.3:  # unary
            par = random.choice(self.d[Real()])

            if m_global_logic in lra_logics:
                new_real = RealOp(random.choice(RealUnOp), par)
            else:
                if random.random() < 0.65 or m_global_logic == 'UFNRA' or m_global_logic == 'NRA' \
                        or m_global_logic == 'QF_UFNRA':
                    new_real = RealOp(random.choice(RealUnOp), par)
                else:  # sin, cos, tanh
                    new_real = RealOp(random.choice(RealUnOp2), par)
            self.d[Real()].append(new_real)
        elif chance < 0.55:  # binary
            try_times = 1
            if m_global_logic in lra_logics:
                try_times = 8
            for _ in range(try_times):  # try more times to success
                real_op_use = random.choice(RealBinOp)
                parone = random.choice(self.d[Real()])
                operands = str(parone)
                partwo = random.choice(self.d[Real()])
                if m_global_logic in lra_logics and real_op_use in ["/", "*"]:
                    if real_op_use == "*":
                        if 'r' in str(parone) or 'uf' in str(parone):
                            partwo = random_real()
                    else:
                        partwo = random_real()
                    operands += (" " + str(partwo))
                    if not ('r' in str(operands) or 'uf' in str(
                            operands)) and random.random() < 0.8:
                        continue
                else:
                    operands += (" " + str(partwo))
                    new_real = RealOp(real_op_use, operands)
                    self.d[Real()].append(new_real)
                    break
        else:  # n-array
            try_times = 1
            if m_global_logic in lra_logics:
                try_times = 8
            for _ in range(try_times):  # try more times to success
                num_real_var = 0
                par = random.choice(self.d[Real()])
                if 'r' in str(par) or 'uf' in str(par):
                    num_real_var += 1
                operands = str(par)
                x = random.randrange(1, 5)
                for _ in range(x):
                    par = random.choice(self.d[Real()])
                    if 'r' in str(par) or 'uf' in str(par):
                        num_real_var += 1
                    operands += (" " + str(par))
                op_to_use = random.choice(RealNOp)
                if m_global_logic in lra_logics:
                    if (op_to_use == "*" or op_to_use ==
                            "/") and num_real_var >= 2:
                        continue
                    else:
                        new_real = RealOp(op_to_use, operands)
                        self.d[Real()].append(new_real)
                        break
                else:
                    new_real = RealOp(op_to_use, operands)
                    self.d[Real()].append(new_real)
                    # break
            # '''
        self.dict[Real()] += 1

        if m_use_ite and random.random() < 0.05:
            parb = random.choice(self.d[Bool()])
            operand = str(parb)
            par1 = random.choice(self.d[Real()])
            operand += (" " + str(par1))
            par2 = random.choice(self.d[Real()])
            operand += (" " + str(par2))
            new_real = IteOp('ite', operand)
            self.d[Real()].append(new_real)

    def bool_from_real(self):
        # n-array or binary?
        if random.random() < 0.5:
            par = random.choice(self.d[Real()])
            operand = str(par)
            par = random.choice(self.d[Real()])
            operand += (" " + str(par))
            new_bool = BoolOp(random.choice(IRNBoolOp), operand)
            self.d[Bool()].append(new_bool)
            return  # stop here

        par = random.choice(self.d[Real()])
        operands = str(par)
        n_operands = random.randrange(1, 6)
        if m_global_logic == "QF_RDL":
            n_operands = 1  # Is this correct for enforcing RDL?

        for _ in range(n_operands):
            par = random.choice(self.d[Real()])
            operands += (" " + str(par))
        new_bool = BoolOp(random.choice(IRNBoolOp), operands)

        if m_test_my_uf and random.random() < 0.1:
            if n_operands == 2:
                new_bool = BoolOp('ufrb3', operands)
            elif n_operands == 3:
                new_bool = BoolOp('ufrb4', operands)
            elif n_operands == 4:
                new_bool = BoolOp('ufrb5', operands)
            elif n_operands == 5:
                new_bool = BoolOp('ufrb6', operands)
            elif n_operands == 6:
                new_bool = BoolOp('ufrb7', operands)

        self.d[Bool()].append(new_bool)
        self.dict[Bool()] += 1

    def fp_from_fp(self):
        chance = random.random()
        if chance < 0.4:  # unary
            par = random.choice(self.d[FP()])
            new_fp = FPOp(random.choice(FPUnOp), par)
            self.d[FP()].append(new_fp)
        else:
            par = random.choice(self.d[FP()])
            operands = str(par)
            par = random.choice(self.d[FP()])
            operands += (" " + str(par))
            new_fp = FPOp(random.choice(FPNOp), operands)
            self.d[FP()].append(new_fp)

    def bool_from_fp(self):
        # n-array or binary?
        if random.random() < 0.15:
            par = random.choice(self.d[FP()])
            operand = str(par)
            new_bool = BoolOp(random.choice(UnFPBoolOp), operand)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1
            return

        par = random.choice(self.d[FP()])
        operands = str(par)
        n_operands = random.randrange(1, 5)
        for _ in range(n_operands):
            par = random.choice(self.d[FP()])
            operands += (" " + str(par))
        new_bool = BoolOp(random.choice(IRNFPBoolOp), operands)
        self.d[Bool()].append(new_bool)
        # give possibility of asserting this new bool here?
        self.dict[Bool()] += 1

    def real_and_int(self):
        chance = random.randint(1, 5)
        if chance <= 2:
            par = random.choice(self.d[Int()])
            self.d[Real()].append(RealOp("to_real", par))
            self.dict[Real()] += 1
        elif chance <= 4:
            par = random.choice(self.d[Real()])
            self.d[Int()].append(IntOp("to_int", par))
            self.dict[Int()] += 1
        else:
            par = random.choice(self.d[Real()])
            self.d[Bool()].append(BoolOp("is_int", par))
            self.dict[Bool()] += 1

    def init_BV(self):
        if True:
            width = random.randint(1, 64)
            # width = random.randint(50000000, 100000000)
            bv_sort = BV(width)
            if bv_sort not in self.d.keys():
                self.d[bv_sort] = []
                self.dict[bv_sort] = 0
            const = VarBV(width, len(self.d[bv_sort]))
            print('(declare-fun {} () {})'.format(const, bv_sort))
            self.d[bv_sort].append(const)
            self.dict[bv_sort] += 1

    def new_BV(self):
        if random.random() < 0.25:
            width = random.randint(1, 64)
            # width = random.randint(50000000, 100000000)
            bv_sort = BV(width)
            if bv_sort not in self.d.keys():
                self.d[bv_sort] = []
                self.dict[bv_sort] = 0
            const = VarBV(width, len(self.d[bv_sort]))
            print('(declare-fun {} () {})'.format(const, bv_sort))
            self.d[bv_sort].append(const)
            self.dict[bv_sort] += 1
        else:
            bv, width = random_BV()
            bv_sort = BV(width)
            if bv_sort not in self.d.keys():
                self.d[bv_sort] = []
                self.dict[bv_sort] = 0
            self.d[bv_sort].append(bv)
            self.dict[bv_sort] += 1

    def BV_from_BV(self):
        options = []
        for o in list(self.d):
            if isinstance(o, BV):
                options.append(o)
        if len(options) > 0:
            s = random.choice(options)
            prob = random.random()

            if m_test_bvint and random.random() < 0.5:
                width = s.w
                par = random.choice(self.d[Int()])
                new_bv = "((_ int2bv " + str(width) + ")" + str(par) + ')'
                self.d[s].append(new_bv)

            if prob < 0.05:  # concat
                if not m_use_bv_concat_repeat:
                    return
                s2 = random.choice(options)
                width = s.w + s2.w
                par1 = random.choice(self.d[s])
                par2 = random.choice(self.d[s2])
                operand = str(par1) + " " + str(par2)
                new_bv = BVOp("concat", operand)
                bv_sort = BV(width)
                if bv_sort not in self.d.keys():
                    self.d[bv_sort] = []
                    self.dict[bv_sort] = 0
                self.d[bv_sort].append(new_bv)
                self.dict[bv_sort] += 1

            elif prob < 0.1:  # repeat
                if not m_use_bv_concat_repeat:
                    return
                ii = random.randint(1, 10)
                width = ii * s.w
                operator = '(_ repeat {})'.format(ii)
                par = random.choice(self.d[s])
                new_bv = BVOp(operator, par)
                bv_sort = BV(width)
                if bv_sort not in self.d.keys():
                    self.d[bv_sort] = []
                    self.dict[bv_sort] = 0
                self.d[bv_sort].append(new_bv)
                self.dict[bv_sort] += 1

            elif prob < 0.2:  # unary, extract
                if random.random() < 0.5:  # unary
                    par = random.choice(self.d[s])
                    new_bv = BVOp(random.choice(Un_BV_BV), par)
                    self.d[s].append(new_bv)
                    self.dict[s] += 1
                else:  # extract
                    width = s.w
                    parameter1 = random.randrange(0, width)
                    parameter2 = random.randint(0, parameter1)
                    operator = "(_ extract {} {})".format(
                        parameter1, parameter2)
                    new_width = parameter1 - parameter2 + 1
                    par = random.choice(self.d[s])
                    new_bv = BVOp(operator, par)
                    bv_sort = BV(new_width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                        self.dict[bv_sort] = 0
                    self.d[bv_sort].append(new_bv)
                    self.dict[bv_sort] += 1

            elif prob < 0.3:
                ii = random.randint(0, 10)
                if random.random() < 0.5:
                    if random.random() < 0.5:
                        operator = "(_ zero_extend {})".format(ii)
                    else:
                        operator = "(_ sign_extend {})".format(ii)
                    width = s.w + ii
                    par = random.choice(self.d[s])
                    new_bv = BVOp(operator, par)
                    bv_sort = BV(width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                        self.dict[bv_sort] = 0
                    self.d[bv_sort].append(new_bv)
                    self.dict[bv_sort] += 1
                else:
                    if random.random() < 0.5:
                        operator = "(_ rotate_left {})".format(ii)
                    else:
                        operator = "(_ rotate_right {})".format(ii)
                    par = random.choice(self.d[s])
                    new_bv = BVOp(operator, par)
                    self.d[s].append(new_bv)
                    self.dict[s] += 1

            elif prob < 0.4:  # n-array
                a = random.randint(1, 3)
                par = random.choice(self.d[s])
                operand = str(par)
                for _ in range(a):
                    par = random.choice(self.d[s])
                    operand += (" " + str(par))
                new_bv = BVOp(random.choice(N_BV_BV), operand)
                self.d[s].append(new_bv)
                self.dict[s] += 1

            else:  # binary
                par1 = random.choice(self.d[s])
                par2 = random.choice(self.d[s])
                operand = str(par1) + " " + str(par2)
                operator = random.choice(Bin_BV_BV)
                new_bv = BVOp(operator, operand)
                if operator == "bvcomp":
                    if BV(1) not in self.d.keys():
                        self.d[BV(1)] = []
                        self.dict[BV(1)] = 0
                    self.d[BV(1)].append(new_bv)
                    self.dict[BV(1)] += 1
                else:
                    self.d[s].append(new_bv)
                    self.dict[s] += 1

    def bool_from_BV(self):
        options = []
        for o in list(self.d):
            if isinstance(o, BV):
                options.append(o)
        if len(options) > 0:
            s = random.choice(options)
            if random.random() < 0.33:
                par1 = random.choice(self.d[s])
                par2 = random.choice(self.d[s])
                operand = str(par1) + " " + str(par2)
                new_bool = BoolOp(random.choice(Bin_BV_Bool), operand)
            else:
                par = random.choice(self.d[s])
                operand = str(par)
                n = random.randint(1, 4)
                for _ in range(n):
                    par = random.choice(self.d[s])
                    operand += (" " + str(par))
                new_bool = BoolOp(random.choice(N_BV_Bool), operand)
            self.d[Bool()].append(new_bool)
            self.dict[Bool()] += 1

    def new_array(self, logic):

        arr_arith_logic = [
            'ANIA',
            'ALIA',
            'AUFNIA',
            'AUFLIA',
            'QF_ANIA',
            'QF_ALIA',
            'QF_AUFNIA',
            'QF_AUFLIA',
            'ANRA',
            'ALRA',
            'AUFNRA',
            'AUFLRA',
            'QF_ANRA',
            'QF_ALRA',
            'QF_AUFNRA',
            'QF_AUFLRA',
            'QF_ALIRA',
            'QF_ANIRA',
            'QF_AUFLIRA',
            'QF_AUFNIRA',
            'ALIRA',
            'ANIRA',
            'AUFLIRA',
            'AUFNIRA']
        if logic == 'ALL' or logic == 'QF_AX' or logic == 'AX':
            ops = []
            for o in list(self.d):
                if not isinstance(o, Arr):
                    ops.append(o)
                if isinstance(o, Arr):
                    if len(self.d[o]) > 0:
                        ops.append(o)
            if len(ops) < 1:
                return  # err handling
            isort = random.choice(ops)
            esort = random.choice(ops)
            arrsort = Arr(isort, esort)
            if arrsort not in list(self.d):
                self.d[arrsort] = []
                self.dict[arrsort] = 0
            n = len(self.d[arrsort])
            new_arr = VarArr(isort, esort, n)
            print('(declare-fun {} () {})'.format(new_arr, arrsort))
            self.d[arrsort].append(new_arr)
            self.dict[arrsort] += 1
        elif logic == 'QF_ABV' or logic == 'QF_AUFBV' or logic == 'ABV' or logic == 'AUFBV':
            ops = []
            for o in list(self.d):
                if not isinstance(o, Arr):
                    ops.append(o)
                if isinstance(o, Arr):
                    if len(self.d[o]) > 0:
                        ops.append(o)
            i_ops = []
            for o in list(self.d):
                if isinstance(o, BV) and len(self.d[o]) > 0:
                    i_ops.append(o)

            if len(i_ops) < 1 or len(ops) < 1:
                return  # err handling

            isort = random.choice(i_ops)
            esort = random.choice(ops)
            arrsort = Arr(isort, esort)
            if arrsort not in list(self.d):
                self.d[arrsort] = []
                self.dict[arrsort] = 0
            n = len(self.d[arrsort])
            new_arr = VarArr(isort, esort, n)
            print('(declare-fun {} () {})'.format(new_arr, arrsort))
            self.d[arrsort].append(new_arr)
            self.dict[arrsort] += 1

        elif logic in arr_arith_logic:
            ops = []
            for o in list(self.d):
                if not isinstance(o, Arr):
                    ops.append(o)
                if isinstance(o, Arr):
                    if len(self.d[o]) > 0:
                        ops.append(o)
            if len(ops) < 1:
                return  # err handling
            isort = random.choice(ops)
            esort = random.choice(ops)
            arrsort = Arr(isort, esort)
            if arrsort not in list(self.d):
                self.d[arrsort] = []
                self.dict[arrsort] = 0
            n = len(self.d[arrsort])
            new_arr = VarArr(isort, esort, n)
            print('(declare-fun {} () {})'.format(new_arr, arrsort))
            self.d[arrsort].append(new_arr)
            self.dict[arrsort] += 1

    def array_from_array(self):
        ops = []
        options = []
        for o in list(self.d):
            if isinstance(o, Arr):
                ops.append(o)
        for things in ops:
            if len(self.d[things]) > 0 and len(self.d[things.sort_index]) > 0 and len(
                    self.d[things.sort_element]) > 0:
                options.append(things)
        if len(options) > 0:
            current_sort = random.choice(options)
            isort = current_sort.sort_index
            esort = current_sort.sort_element
            par = random.choice(self.d[current_sort])
            par2 = random.choice(self.d[isort])
            par3 = random.choice(self.d[esort])
            items = '{} {} {}'.format(par, par2, par3)
            new_arr = ArrOp('store', items)
            self.d[current_sort].append(new_arr)
            self.dict[current_sort] += 1

    def bool_from_array(self):
        if random.random() < 0.5:
            ops = []
            options = []
            for o in list(self.d):
                if isinstance(o, Arr):
                    ops.append(o)
            for things in ops:
                if len(self.d[things]) > 0 and len(
                        self.d[things.sort_index]) > 0:
                    options.append(things)
            if len(options) > 0:
                current_sort = random.choice(options)
                isort = current_sort.sort_index
                par = random.choice(self.d[current_sort])
                par2 = random.choice(self.d[isort])
                expression = '{} {}'.format(par, par2)
                new_one = ArrOp('select', expression)
                sssort = current_sort.sort_element
                self.d[sssort].append(new_one)
                if sssort not in self.dict.keys():
                    self.dict[sssort] = 0
                self.dict[sssort] += 1
        else:  # STP does not support array extensionality  (e.g.. arr1 = arr2)
            ops = []
            options = []
            for o in list(self.d):
                if isinstance(o, Arr):
                    ops.append(o)
            for things in ops:
                if len(self.d[things]) > 0:
                    options.append(things)
            if len(options) > 0:
                current_sort = random.choice(options)
                par = random.choice(self.d[current_sort])
                operand = str(par)
                n = random.randint(1, 4)
                for _ in range(n):
                    par = random.choice(self.d[current_sort])
                    operand += (" " + str(par))
                if random.random() < 0.5:
                    new_bool = BoolOp('=', operand)
                else:
                    new_bool = BoolOp('distinct', operand)
                self.d[Bool()].append(new_bool)
                self.dict[Bool()] += 1

                #  (eqrange a1 a2 (- 1) 1))
                if m_test_eqrange and random.random() < 0.3:
                    current_sort = random.choice(options)
                    par1 = random.choice(self.d[current_sort])
                    operand = str(par1)
                    par2 = random.choice(self.d[current_sort])
                    operand += (" " + str(par2))
                    operand += (" " + str(random.randint(1, 5)))
                    operand += (" " + str(random.randint(6, 15)))
                    new_bool = BoolOp('eqrange', operand)
                    self.d[Bool()].append(new_bool)

    def bool_from_bool(self):
        p = random.randint(1, 7)
        if p == 1:
            # pick Unary
            par = random.choice(self.d[Bool()])
            new_bool = BoolOp(random.choice(UnOp), par)
        elif p == 2:
            # pick Binary
            par1 = random.choice(self.d[Bool()])
            par2 = random.choice(self.d[Bool()])
            operand = str(par1)
            operand += (" " + str(par2))
            new_bool = BoolOp(random.choice(BiOp), operand)
        else:
            n_operands = random.randint(1, 6)
            par = random.choice(self.d[Bool()])
            operands = str(par)
            for _ in range(n_operands):
                par = random.choice(self.d[Bool()])
                operands += (" " + str(par))

            new_bool = BoolOp(random.choice(NarOp), operands)
            if m_test_my_uf and random.random() < 0.1:
                ufpr = random.random()
                if n_operands == 2:
                    if ufpr < 0.5:
                        new_bool = BoolOp('uf3', operands)
                    else:
                        new_bool = BoolOp('uf3_2', operands)
                    # else: new_bool = Bool_Op('uf3_3', operands)
                elif n_operands == 3:
                    if ufpr < 0.5:
                        new_bool = BoolOp('uf4', operands)
                    else:
                        new_bool = BoolOp('uf4_2', operands)
                    # else: new_bool = Bool_Op('uf4_3', operands)
                elif n_operands == 4:
                    if ufpr < 0.5:
                        new_bool = BoolOp('uf5', operands)
                    else:
                        new_bool = BoolOp('uf5_2', operands)
                    # else: new_bool = Bool_Op('uf5_3', operands)
                elif n_operands == 5:
                    if ufpr < 0.5:
                        new_bool = BoolOp('uf6', operands)
                    else:
                        new_bool = BoolOp('uf6_2', operands)
                    # else: new_bool = Bool_Op('uf6_3', operands)
                elif n_operands == 6:
                    if ufpr < 0.5:
                        new_bool = BoolOp('uf7', operands)
                    else:
                        new_bool = BoolOp('uf7_2', operands)
                    # else: new_bool = Bool_Op('uf7_3', operands)

        self.d[Bool()].append(new_bool)
        self.dict[Bool()] += 1

        if m_use_ite and random.random() < 0.05:
            parb = random.choice(self.d[Bool()])
            operand = str(parb)
            par1 = random.choice(self.d[Bool()])
            operand += (" " + str(par1))
            par2 = random.choice(self.d[Bool()])
            operand += (" " + str(par2))
            new_bb2 = IteOp('ite', operand)
            self.d[Bool()].append(new_bb2)

        return new_bool

    def bool_choice(self):
        return random.choice(self.d[Bool()])

    def num_bool(self):
        return min(len(self.d[Bool()]), 20)

    def bool_sample(self, nvar):
        bool_idx = random.sample(range(len(self.d[Bool()])), nvar)
        sample = []
        for x in bool_idx:
            sample.append(self.d[Bool()][x])
        return sample


UnOp = ["not"]
BiOp = ["=>"]
NarOp = ["and", "or", "xor", "=", "distinct"]
IntUnOp = ["-", "abs"]
IntBinOp = ["div", "mod", "*", "-", "+"]
IntNOp = ["-", "+", "*"]
IRNBoolOp = ["<=", "<", ">=", ">", "=", "distinct"]
RealBinOp = ["-", "+", "*", "/"]
RealNOp = ["-", "+", "*"]
RealUnOp = ["-"]  #
RealUnOp2 = ["-", "abs", "-", "abs"]
# i "sin", "tanh"]
RDLBinOp = ["-"]
# "sin" "tanh"] #for NRA
# RealUnOp = ["-"]

'''
Bag
'''
# union_max, union_disjoint, intersection_min, difference_subtract, difference_remove, bag.is_included
# emptybag, bag.count, mkBag, bag.card, bag.choose, bag.is_singleton
BagUnOp = ['']
BagUnIp = ['mkBag']
BagBinOp = [
    'union_disjoint',
    'union_max',
    'intersection_min',
    'difference_remove']
IRNBagBoolOp = ['bag.is_included']

'''
#Set
'''
# transpose
# union, intersection, setminus, is_singleton, join, product, member, insert, complement, subset, set-has-size, card
SetUnOp = ['complement']  # OK?
SetBinOp = ['union', 'intersection', 'setminus']
IRNSetBoolOp = ['subset']

'''
# String
'''
# Reference: http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml
# str.to_int, str.from_int, int.to.str

# not stable: str.from_code
StringUnOp = ['str.len']
StringBinOp = ['str.++']
StringNOp = ['str.++']
# str.substr, str.replace, str.indexof, str.prefixof, str.at, str.replace_all
StringBinBoolOp = [
    'str.<=',
    'str.<',
    'str.contains',
    'str.suffixof',
    'str.prefixof']
if m_use_swarm_str:
    StringBinBoolOp = random.sample(StringBinBoolOp, 3)

StringNBoolOp = ['distinct', '=']

ReUnOp = ['re.opt', 're.comp', 're.*', 're.+']
ReBinOp = ['re.++', 're.union', 're.diff', 're.inter']
if m_use_swarm_str:
    ReUnOp = random.sample(ReUnOp, 2)
    ReBinOp = random.sample(ReBinOp, 2)

# Separation logic in CVC4
# http://cvc4.cs.stanford.edu/wiki/Separation_Logic
SeplogBinOp = ['pto']
SeplogNBoolOp = ['wand', 'sep']

# Float16 is a synonym for (_ FloatingPoint  5  11)
# Float32 is a synonym for (_ FloatingPoint  8  24)
# Float64 is a synonym for (_ FloatingPoint 11  53)
# Float128 is a synonym for (_ FloatingPoint 15 113)
'''
 :funs ((roundNearestTiesToEven RoundingMode) (RNE RoundingMode)
        (roundNearestTiesToAway RoundingMode) (RNA RoundingMode)
        (roundTowardPositive RoundingMode)    (RTP RoundingMode)
        (roundTowardNegative RoundingMode)    (RTN RoundingMode)
        (roundTowardZero RoundingMode)        (RTZ RoundingMode)
        )
'''
# See http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml
# TODO: use other op in  UnFpBoolOp
UnFPBoolOp = [
    'fp.isPositive',
    'fp.isNormal',
    'fp.isNegative',
    'fp.isNaN',
    'fp.isSubnormal',
    'fp.isInfinite',
    'fp.isZero']
IRNFPBoolOp = ['fp.leq', 'fp.lt', 'fp.eq', 'fp.geq', 'fp.gt']

FPNOp = []
FPTriOp = []
FPUnOp = []
if m_fp_rounding_mode == 'random':
    FPNOp = [
        'fp.add RNE',
        'fp.add RNA',
        'fp.add RTP',
        'fp.add RTN',
        'fp.add RTZ',
        'fp.sub RNE',
        'fp.sub RNA',
        'fp.sub RTP',
        'fp.sub RTN',
        'fp.sub RTZ',
        'fp.mul RNE',
        'fp.mul RNA',
        'fp.mul RTP',
        'fp.mul RTN',
        'fp.mul RTZ',
        'fp.div RNE',
        'fp.div RNA',
        'fp.div RTP',
        'fp.div RTN',
        'fp.div RTZ',
        'fp.rem',
        'fp.rem',
        'fp.rem',
        'fp.rem',
        'fp.min',
        'fp.min',
        'fp.min',
        'fp.min',
        'fp.max',
        'fp.max',
        'fp.max',
        'fp.max']
    # if m_use_swarm_fp:
    #    FPNOp = random.sample(FPNOp, 10)
    FPTriOp = [
        'fp.fma RNE',
        'fp.fma RNA',
        'fp.fma RTP',
        'fp.fma RTN',
        'fp.fma RTZ']
    FPUnOp = ['fp.sqrt RNE', 'fp.sqrt RNA',
              'fp.abs', 'fp.abs', 'fp.abs',
              'fp.neg', 'fp.neg', 'fp.neg'
              ]
else:
    FPNOp = ["fp.add " + m_fp_rounding_mode, "fp.sub " + m_fp_rounding_mode,
             "fp.mul " + m_fp_rounding_mode, "fp.div " + m_fp_rounding_mode,
             "fp.rem", "fp.min", "fp.max"]
    FPTriOp = ["fp.fma " + m_fp_rounding_mode]
    FPUnOp = ["fp.sqrt " + m_fp_rounding_mode, "fp.abs", "fp.neg"]

############

Bin_BV_BV = [
    "bvand",
    "bvor",
    "bvadd",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvshl",
    "bvlshr",
    "bvnand",
    "bvnor",
    "bvsub",
    "bvsdiv",
    "bvsrem",
    "bvsmod",
    "bvashr",
    "bvcomp",
    "bvxnor"]
if m_use_swarm_bv:
    Bin_BV_BV = random.sample(Bin_BV_BV, 3)

# N_BV_BV = ["bvxor"]
N_BV_BV = ["bvxor", "bvor", "bvand"]
if m_use_swarm_bv:
    N_BV_BV = random.sample(N_BV_BV, 1)

Un_BV_BV = ["bvnot", "bvneg"]
Bin_BV_Bool = [
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge"]
N_BV_Bool = ["=", "distinct"]


def add_smt_opt_cmd(nodes, logic):
    if m_test_smt_opt:
        nodes_vars = []
        nodes_bv_vars = []
        if (logic in qf_real_logic_options or logic in qf_ira_logics) and len(
                nodes.d[Real()]) > 0:
            for rv in nodes.d[Real()]:
                if isinstance(rv, VarReal) and random.random() < 0.9:
                    nodes_vars.append(rv)
        if (logic in qf_int_logic_options or logic in qf_ira_logics) and len(
                nodes.d[Int()]) > 0:
            for rv in nodes.d[Int()]:
                if isinstance(rv, VarInt) and random.random() < 0.9:
                    nodes_vars.append(rv)

        if logic in qf_bv_logic_options:
            for width in range(0, 64):
                bv_sort = BV(width)
                if bv_sort not in nodes.d.keys():
                    continue
                for rv in nodes.d[bv_sort]:
                    if isinstance(rv, VarBV) and random.random() < 0.98:
                        nodes_bv_vars.append(rv)
                        if random.random() < 0.6:
                            print('(minimize {})'.format(rv))
                        else:
                            print('(maximize {})'.format(rv))

        # tes bv octagon
        if len(nodes_bv_vars) >= 2:
            # print(";BV OCT!")
            octagon_cnts = list(
                itertools.combinations(
                    nodes_bv_vars,
                    2))  # octagon domain?
            for v1, v2 in octagon_cnts:
                if v1.sort == v2.sort:
                    if random.random() < 0.5:
                        print('(minimize (bvadd {} {}))'.format(v1, v2))
                    else:
                        print('(maximize (bvsub {} {}))'.format(v1, v2))

        # use non-stndard domain
        if m_test_smt_opt_fancy_term:
            tmp_num_goal = 0
            if (logic in qf_real_logic_options or logic in qf_ira_logics) and len(
                    nodes.d[Real()]) > 0:
                for rv in nodes.d[Real()]:
                    if isinstance(rv, VarReal):
                        continue
                    else:
                        if random.random() < 0.5:
                            print('(minimize {})'.format(rv))
                        else:
                            print('(maximize {})'.format(rv))
                        tmp_num_goal += 1
                        if tmp_num_goal >= 15:
                            break
            if (logic in qf_int_logic_options or logic in qf_ira_logics) and len(
                    nodes.d[Int()]) > 0:
                for rv in nodes.d[Int()]:
                    if isinstance(rv, VarInt):
                        continue
                    else:
                        if random.random() < 0.5:
                            print('(minimize {})'.format(rv))
                        else:
                            print('(maximize {})'.format(rv))
                        tmp_num_goal += 1
                        if tmp_num_goal >= 15:
                            break
            if logic in qf_bv_logic_options:
                for width in range(0, 64):
                    bv_sort = BV(width)
                    if bv_sort not in nodes.d.keys():
                        continue
                    for rv in nodes.d[bv_sort]:
                        if isinstance(rv, VarBV):
                            continue
                        else:
                            if random.random() < 0.6:
                                print('(minimize {})'.format(rv))
                            else:
                                print('(maximize {})'.format(rv))
                            tmp_num_goal += 1
                            if tmp_num_goal >= 15:
                                break

        elif len(nodes_vars) >= 3:
            opt_ty = random.random()
            if opt_ty < 0.3:  # inerval domain??
                num_query = 0
                for rv in nodes_vars:
                    num_query += 1
                    if num_query > 15:
                        break
                    if random.random() < 0.6:
                        print('(minimize {})'.format(rv))
                    else:
                        print('(maximize {})'.format(rv))
            elif opt_ty < 0.6:
                octagon_cnts = list(
                    itertools.combinations(
                        nodes_vars, 2))  # octagon domain?
                random.shuffle(octagon_cnts)
                num_query = 0
                for v1, v2 in octagon_cnts:
                    if random.random() < 0.65:
                        num_query += 1
                        if num_query > 15:
                            break
                        if random.random() < 0.6:
                            print('(minimize (+ {} {}))'.format(v1, v2))
                        else:
                            print('(maximize (- {} {}))'.format(v1, v2))
            else:
                octagon_cnts = list(
                    itertools.combinations(
                        nodes_vars, 3))  # octagon domain?
                random.shuffle(octagon_cnts)
                num_query = 0
                for v1, v2, v3 in octagon_cnts:
                    if random.random() < 0.65:
                        num_query += 1
                        if num_query > 15:
                            break
                        if random.random() < 0.6:
                            print('(minimize (+ {} {} {}))'.format(v1, v2, v3))
                        else:
                            print('(maximize (- {} {} {}))'.format(v1, v2, v3))


# Merge all cmds here
def add_additional_cmds(nodes, logic):
    global m_test_named_assert
    if m_test_smt_opt:
        add_smt_opt_cmd(nodes, logic)
    return


def datalog_chc_fuzz(logic, vcratio, cntsize):
    assert m_test_datalog_chc
    global m_test_datalog_chc_logic

    if m_set_logic:
        print('(set-logic HORN)')

    set_options()
    add_reals = -1
    add_ints = -1

    if m_test_datalog_chc_logic == "int":
        add_ints = 1
    elif m_test_datalog_chc_logic == "real":
        add_reals = 1
    elif m_test_datalog_chc_logic == "bv":
        add_ints = 0
        add_reals = 0

    nodes = Nodes(add_ints, add_reals)

    if m_test_datalog_chc_logic == "int":
        rand = random.random()
        if rand < 0.5:
            print("(declare-fun inv-int3 (Int Int Int) Bool)")
        else:
            print("(declare-fun inv-int4 (Int Int Int Int) Bool)")
        sz = random.randint(6, 16)
        for _ in range(sz):
            if rand < 0.5:
                simp = SimpleNodes(['x', 'y', 'z'], "Int")
                term1 = simp.get_int_term()
                term2 = simp.get_int_term()
                term3 = simp.get_int_term()
                bbb = '(inv-int3 {} {} {})'.format(term1, term2, term3)
                predicate = simp.get_bool()
                connect = random.choice(['or'])
                pp = "(assert (forall ((x Int) (y Int) (z Int)) ({} {} {})))".format(
                    connect, bbb, predicate)
            else:
                simp = SimpleNodes(['x', 'y', 'z', 's'], "Int")
                term1 = simp.get_int_term()
                term2 = simp.get_int_term()
                term3 = simp.get_int_term()
                term4 = simp.get_int_term()
                predicate = simp.get_bool()
                connect = random.choice(['or'])
                bbb = '(inv-int4 {} {} {} {})'.format(term1,
                                                      term2, term3, term4)
                pp = "(assert (forall ((x Int) (y Int) (z Int) (s Int)) ({} {} {})))".format(
                    connect, bbb, predicate)
            print(pp)
    elif m_test_datalog_chc_logic == "real":
        rand = random.random()
        if rand < 0.5:
            print("(declare-fun inv-real3 (Real Real Real) Bool)")
        else:
            print("(declare-fun inv-real4 (Real Real Real Real) Bool)")
        sz = random.randint(6, 16)
        for _ in range(sz):
            if rand < 0.5:
                simp = SimpleNodes(['x', 'y', 'z'], "Real")
                term1 = simp.get_real_term()
                term2 = simp.get_real_term()
                term3 = simp.get_real_term()
                bbb = '(inv-real3 {} {} {})'.format(term1, term2, term3)
                predicate = simp.get_bool()
                connect = random.choice(['or'])
                pp = "(assert (forall ((x Real) (y Real) (z Real)) ({} {} {})))".format(
                    connect, bbb, predicate)
            else:
                simp = SimpleNodes(['x', 'y', 'z', 's'], "Real")
                term1 = simp.get_real_term()
                term2 = simp.get_real_term()
                term3 = simp.get_real_term()
                term4 = simp.get_real_term()
                predicate = simp.get_bool()
                bbb = '(inv-real4 {} {} {} {})'.format(term1,
                                                       term2, term3, term4)
                connect = random.choice(['or'])
                pp = "(assert (forall ((x Real) (y Real) (z Real) (s Real)) ({} {} {})))".format(
                    connect, bbb, predicate)
            print(pp)
    else:
        assertions = cntsize
        while assertions > 0:
            nodes.quantifier_chc()
            assertions -= 1


'''
Generate formulas in strint CNF form
# TODO: consider incremental
'''


def strict_cnf_fuz(logic, vcratio, cntsize):
    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals, add_quantifiers = \
        set_logic(logic)

    global m_assert_id, m_all_assertions
    global n_push, n_pop

    nodes = Nodes(add_ints, add_reals)
    if r > 0:
        n_bvs = random.randint(1, 10)
        for _ in range(n_bvs):
            nodes.init_BV()

    if True:  # bool
        assertions = random.randrange(1, cntsize)
        while assertions > 0:
            if n_push > n_pop:
                k = random.randint(1, n_push - n_pop)
                if not m_fancy_push:
                    k = 1
                if random.random() < m_push_pop_rate:
                    nodes.pop(k)
                    n_pop += k
                elif random.random() < m_push_pop_rate:
                    k = random.randint(1, 5)
                    if not m_fancy_push:
                        k = 1
                    nodes.push(k)
                    n_push += k
            if n_push == n_pop:
                if random.random() < m_push_pop_rate:
                    k = random.randint(1, 5)
                    if not m_fancy_push:
                        k = 1
                    nodes.push(k)
                    n_push += k

            if random.random() < 0.2:
                prob = random.random()
                if prob < a:
                    nodes.newSort()
                elif prob < b:
                    nodes.varUSort()
                elif prob < c:
                    nodes.bool_from_usort()
            if random.random() < ni:
                nodes.new_int()
            if random.random() < e:
                if m_test_string:
                    nodes.string_from_string()
                elif m_test_string_lia:
                    nodes.int_from_int()
                    nodes.string_from_string()
                else:
                    nodes.int_from_int()
                if m_test_set_bapa and random.random() < 0.6:
                    nodes.set_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bag_from_bag()

            if random.random() < f:
                if m_test_string:
                    nodes.bool_from_string()
                elif m_test_string_lia:
                    nodes.bool_from_int()
                    nodes.bool_from_string()
                else:
                    nodes.bool_from_int()
                if m_test_set_bapa and random.random() < 0.6:
                    nodes.bool_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bool_from_bag()
                if m_test_seplog and random.random() < 0.6:
                    nodes.bool_from_seplog()
            if random.random() < g:
                if m_test_fp:
                    nodes.new_fp()
                elif m_test_fp_lra:
                    nodes.new_fp()
                    nodes.new_real()
                else:
                    nodes.new_real()
            if random.random() < h:
                if m_test_fp:
                    nodes.fp_from_fp()
                elif m_test_fp_lra:
                    nodes.fp_from_fp()
                    nodes.real_from_real()
                else:
                    nodes.real_from_real()
            if random.random() < m:
                if m_test_fp:
                    nodes.bool_from_fp()
                elif m_test_fp_lra:
                    nodes.bool_from_fp()
                    nodes.bool_from_real()
                else:
                    nodes.bool_from_real()
            if random.random() < v:
                nodes.real_and_int()
            if random.random() < r:
                nodes.new_BV()
            if random.random() < t:
                nodes.BV_from_BV()
            if random.random() < u:
                nodes.bool_from_BV()
            if random.random() < gen_arr:
                nodes.new_array(logic)
            if random.random() < gen_arr:
                nodes.bool_from_array()
            if random.random() < add_quantifiers:
                nodes.quantifier()

            if random.random() < 0.5:
                if random.random() < 0.22:
                    par1 = random.choice(nodes.d[Bool()])
                    par2 = random.choice(nodes.d[Bool()])
                    operand = str(par1)
                    operand += (" " + str(par2))
                    new_node = BoolOp("or", operand)
                else:
                    n_operands = random.randint(1, 15)
                    par = random.choice(nodes.d[Bool()])
                    operands = str(par)
                    for _ in range(n_operands):
                        if random.random() < 0.33:
                            par = random.choice(nodes.d[Bool()])
                            operands += (" " + str(par))
                        else:
                            par = random.choice(nodes.d[Bool()])
                            new_par = BoolOp("not", par)
                            operands += (" " + str(new_par))
                    new_node = BoolOp("or", operands)

                if m_test_max_smt or m_test_max_sat:
                    if random.random() < m_max_smt_rate:
                        print('(assert {})'.format(new_node))
                    else:
                        # print('(assert-soft {})'.format(new_node))
                        print('(assert-soft {} :weight {})'.format(new_node,
                              str(random.randint(1, 20))))
                elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                    m_assert_id += 1
                    print(
                        '(assert (! ' +
                        format(new_node) +
                        ' :named IP_' +
                        str(m_assert_id) +
                        '))')
                    m_all_assertions.append('IP_' + str(m_assert_id))
                else:
                    print('(assert {})'.format(new_node))

            assertions -= 1

            if random.random() < 0.05:
                if m_reset_assert and random.random() < 0.3:
                    print(m_reset_cmd)
                print('(check-sat)')
                if m_test_smt_opt:
                    print('(get-objectives)')
                if (m_test_unsat_core or m_test_proof or m_test_named_assert) and random.random(
                ) < 0.5:
                    tmp_num_goal = 0
                    cur_all_ass = m_all_assertions
                    if len(cur_all_ass) >= 2:
                        octele_cnts = list(
                            itertools.combinations(
                                cur_all_ass, 2))
                        random.shuffle(octele_cnts)
                        for cnt_a, cnt_b in octele_cnts:
                            print(
                                "(check-sat-assuming (" + cnt_a + " " + cnt_b + "))")
                            if m_test_unsat_core:
                                print("(get-unsat-core)")
                            tmp_num_goal += 1
                            if tmp_num_goal == 5:
                                break

        add_additional_cmds(nodes, logic)


# I merge other incremental tacitcs here (but remove push/pop and check-sat)
def non_inc_fuzz(logic, vcratio, cntsize):
    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals, add_quantifiers = \
        set_logic(logic)

    nodes = Nodes(add_ints, add_reals)
    if r > 0:
        n_bvs = random.randint(1, 10)
        for _ in range(n_bvs):
            nodes.init_BV()

    global m_assert_id, m_all_assertions

    monic_tactic = random.random()
    # monic_tactic = 0.2
    # integrate bool, cnf, ncnf, CNFexp into non_inc_fuzz
    # CNFexp is mem and time-consuming
    if monic_tactic < 0.25:  # bool
        assertions = random.randrange(0, cntsize)
        while assertions > 0:
            if random.random() < 0.2:
                prob = random.random()
                if prob < a:
                    nodes.newSort()
                elif prob < b:
                    nodes.varUSort()
                elif prob < c:
                    nodes.bool_from_usort()
            if random.random() < m_create_bool_rate:
                nodes.new_bool()
            if random.random() < ni:
                nodes.new_int()
            if random.random() < e:
                if m_test_string:
                    nodes.string_from_string()
                elif m_test_string_lia:
                    nodes.int_from_int()
                    nodes.string_from_string()
                else:
                    nodes.int_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.set_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bag_from_bag()

            if random.random() < f:
                if m_test_string:
                    nodes.bool_from_string()
                elif m_test_string_lia:
                    nodes.bool_from_int()
                    nodes.bool_from_string()
                else:
                    nodes.bool_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.bool_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bool_from_bag()
                if m_test_seplog and random.random() < 0.6:
                    nodes.bool_from_seplog()
            if random.random() < g:
                if m_test_fp:
                    nodes.new_fp()
                elif m_test_fp_lra:
                    nodes.new_fp()
                    nodes.new_real()
                else:
                    nodes.new_real()
            if random.random() < h:
                if m_test_fp:
                    nodes.fp_from_fp()
                elif m_test_fp_lra:
                    nodes.fp_from_fp()
                    nodes.real_from_real()
                else:
                    nodes.real_from_real()
            if random.random() < m:
                if m_test_fp:
                    nodes.bool_from_fp()
                elif m_test_fp_lra:
                    nodes.bool_from_fp()
                    nodes.bool_from_real()
                else:
                    nodes.bool_from_real()
            if random.random() < v:
                nodes.real_and_int()
            if random.random() < r:
                nodes.new_BV()
            if random.random() < t:
                nodes.BV_from_BV()
            if random.random() < u:
                nodes.bool_from_BV()
            if random.random() < gen_arr:
                nodes.new_array(logic)
            if random.random() < gen_arr:
                nodes.bool_from_array()
            if random.random() < add_quantifiers:
                nodes.quantifier()

            if random.random() < m_assert_or_create_new:
                new_node = nodes.bool_choice()
            else:
                new_node = nodes.bool_from_bool()

            if random.random() < 0.33:
                if m_test_max_smt or m_test_max_sat:
                    if random.random() < m_max_smt_rate:
                        print('(assert {})'.format(new_node))
                    else:
                        # print('(assert-soft {})'.format(new_node))
                        print('(assert-soft {} :weight {})'.format(new_node,
                              str(random.randint(1, 20))))
                elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                    # maxsmt and unsat_core do not conflict. TODO: core for
                    # maxsmt
                    m_assert_id += 1
                    print(
                        '(assert (! ' +
                        format(new_node) +
                        ' :named IP_' +
                        str(m_assert_id) +
                        '))')
                    m_all_assertions.append('IP_' + str(m_assert_id))
                else:
                    print('(assert {})'.format(new_node))
                assertions -= 1

    elif monic_tactic < 0.5:  # cnf
        for _ in range(cntsize):
            if random.random() < 0.2:
                prob = random.random()
                if prob < a:
                    nodes.newSort()
                elif prob < b:
                    nodes.varUSort()
                elif prob < c:
                    nodes.bool_from_usort()

            if random.random() < m_create_bool_rate:
                nodes.new_bool()
            if random.random() < ni:
                nodes.new_int()
            if random.random() < e:
                # nodes.int_from_int()
                if m_test_string:
                    nodes.string_from_string()
                elif m_test_string_lia:
                    nodes.int_from_int()
                    nodes.string_from_string()
                else:
                    nodes.int_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.set_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bag_from_bag()

            if random.random() < f:
                # nodes.bool_from_int()
                if m_test_string:
                    nodes.bool_from_string()
                elif m_test_string_lia:
                    nodes.bool_from_int()
                    nodes.bool_from_string()
                else:
                    nodes.bool_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.bool_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bool_from_bag()

                if m_test_seplog and random.random() < 0.6:
                    nodes.bool_from_seplog()
            if random.random() < g:
                if m_test_fp:
                    nodes.new_fp()
                elif m_test_fp_lra:
                    nodes.new_fp()
                    nodes.new_real()
                else:
                    nodes.new_real()
            if random.random() < h:
                if m_test_fp:
                    nodes.fp_from_fp()
                elif m_test_fp_lra:
                    nodes.fp_from_fp()
                    nodes.real_from_real()
                else:
                    nodes.real_from_real()
            if random.random() < m:
                if m_test_fp:
                    nodes.bool_from_fp()
                elif m_test_fp_lra:
                    nodes.bool_from_fp()
                    nodes.bool_from_real()
                else:
                    nodes.bool_from_real()
            if random.random() < v:
                nodes.real_and_int()
            if random.random() < r:
                nodes.new_BV()
            if random.random() < t:
                nodes.BV_from_BV()
            if random.random() < u:
                nodes.bool_from_BV()
            if random.random() < gen_arr:
                nodes.new_array(logic)
            if random.random() < gen_arr:
                nodes.array_from_array()
            if random.random() < gen_arr:
                nodes.bool_from_array()
            if random.random() < add_quantifiers:
                nodes.quantifier()

            if random.random() < m_assert_or_create_new:
                new_node = nodes.bool_choice()
            else:
                new_node = nodes.bool_from_bool()

            if random.random() < 0.3:
                if m_test_max_smt or m_test_max_sat:
                    if random.random() < m_max_smt_rate:
                        print('(assert {})'.format(new_node))
                    else:
                        # print('(assert-soft {})'.format(new_node))
                        print('(assert-soft {} :weight {})'.format(new_node,
                              str(random.randint(1, 20))))
                elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                    m_assert_id += 1
                    print(
                        '(assert (! ' +
                        format(new_node) +
                        ' :named IP_' +
                        str(m_assert_id) +
                        '))')
                    m_all_assertions.append('IP_' + str(m_assert_id))
                else:
                    print('(assert {})'.format(new_node))

        upp_b = nodes.num_bool()
        n_variables, n_clauses = Ratio(1, upp_b, vcratio)
        bank = nodes.bool_sample(n_variables)
        clauses = Clauses(bank, n_clauses)
        clauses.new_cnfs()

    elif monic_tactic < 0.75:  # cnf
        for _ in range(cntsize):
            if random.random() < 0.2:
                prob = random.random()
                if prob < a:
                    nodes.newSort()
                elif prob < b:
                    nodes.varUSort()
                elif prob < c:
                    nodes.bool_from_usort()
            if random.random() < m_create_bool_rate:
                nodes.new_bool()
            if random.random() < ni:
                nodes.new_int()
            if random.random() < e:
                if m_test_string:
                    nodes.string_from_string()
                elif m_test_string_lia:
                    nodes.int_from_int()
                    nodes.string_from_string()
                else:
                    nodes.int_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.set_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bag_from_bag()

            if random.random() < f:
                if m_test_string:
                    nodes.bool_from_string()
                elif m_test_string_lia:
                    nodes.bool_from_int()
                    nodes.bool_from_string()
                else:
                    nodes.bool_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.bool_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bool_from_bag()
                if m_test_seplog and random.random() < 0.7:
                    nodes.bool_from_seplog()
            if random.random() < g:
                if m_test_fp:
                    nodes.new_fp()
                elif m_test_fp_lra:
                    nodes.new_fp()
                    nodes.new_real()
                else:
                    nodes.new_real()
            if random.random() < h:
                if m_test_fp:
                    nodes.fp_from_fp()
                elif m_test_fp_lra:
                    nodes.fp_from_fp()
                    nodes.real_from_real()
                else:
                    nodes.real_from_real()
            if random.random() < m:
                if m_test_fp:
                    nodes.bool_from_fp()
                elif m_test_fp_lra:
                    nodes.bool_from_fp()
                    nodes.bool_from_real()
                else:
                    nodes.bool_from_real()
            if random.random() < v:
                nodes.real_and_int()
            if random.random() < r:
                nodes.new_BV()
            if random.random() < t:
                nodes.BV_from_BV()
            if random.random() < u:
                nodes.bool_from_BV()
            if random.random() < m_create_bool_rate:
                nodes.bool_from_bool()
            if random.random() < gen_arr:
                nodes.new_array(logic)
            if random.random() < gen_arr:
                nodes.array_from_array()
            if random.random() < gen_arr:
                nodes.bool_from_array()
            if random.random() < add_quantifiers:
                nodes.quantifier()

        upp_b = nodes.num_bool()
        n_variables, n_clauses = Ratio(1, upp_b, vcratio)
        bank = nodes.bool_sample(n_variables)
        clauses = Clauses(bank, n_clauses)
        clauses.new_dist_cnfs()

    # '''
    else:  # CNFExp
        for _ in range(cntsize):
            if random.random() < 0.2:
                prob = random.random()
                if prob < a:
                    nodes.newSort()
                elif prob < b:
                    nodes.varUSort()
                elif prob < c:
                    nodes.bool_from_usort()

            if random.random() < m_create_bool_rate:
                nodes.new_bool()
            if random.random() < ni:
                nodes.new_int()
            if random.random() < e:
                if m_test_string:
                    nodes.string_from_string()
                elif m_test_string_lia:
                    nodes.int_from_int()
                    nodes.string_from_string()
                else:
                    nodes.int_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.set_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bag_from_bag()

            if random.random() < f:
                if m_test_string:
                    nodes.bool_from_string()
                elif m_test_string_lia:
                    nodes.bool_from_int()
                    nodes.bool_from_string()
                else:
                    nodes.bool_from_int()

                if m_test_set_bapa and random.random() < 0.6:
                    nodes.bool_from_set()
                if m_test_bag_bapa and random.random() < 0.6:
                    nodes.bool_from_bag()
                if m_test_seplog and random.random() < 0.7:
                    nodes.bool_from_seplog()
            if random.random() < g:
                if m_test_fp:
                    nodes.new_fp()
                elif m_test_fp_lra:
                    nodes.new_fp()
                    nodes.new_real()
                else:
                    nodes.new_real()
            if random.random() < h:
                if m_test_fp:
                    nodes.fp_from_fp()
                elif m_test_fp_lra:
                    nodes.fp_from_fp()
                    nodes.real_from_real()
                else:
                    nodes.real_from_real()
            if random.random() < m:
                if m_test_fp:
                    nodes.bool_from_fp()
                elif m_test_fp_lra:
                    nodes.bool_from_fp()
                    nodes.bool_from_real()
                else:
                    nodes.bool_from_real()

            if random.random() < v:
                nodes.real_and_int()
            if random.random() < r:
                nodes.new_BV()
            if random.random() < t:
                nodes.BV_from_BV()
            if random.random() < u:
                nodes.bool_from_BV()
            if random.random() < m_create_bool_rate:
                nodes.bool_from_bool()
            if random.random() < gen_arr:
                nodes.new_array(logic)
            if random.random() < gen_arr:
                nodes.array_from_array()
            if random.random() < gen_arr:
                nodes.bool_from_array()
            if random.random() < add_quantifiers:
                nodes.quantifier()

        upp_b = nodes.num_bool()
        n_variables, n_clauses = Ratio(1, upp_b, vcratio)
        bank = nodes.bool_sample(n_variables)
        clauses = Clauses(bank, n_clauses)
        clauses.new_cnfs()

        assertions = random.randrange(0, cntsize)
        while assertions > 0:

            if random.random() < 0.5:
                new_node = clauses.cnf_choice()
            else:
                new_node = clauses.node_from_cnf()

            if random.random() < 0.6:
                if m_test_max_smt or m_test_max_sat:
                    if random.random() < m_max_smt_rate:
                        print('(assert {})'.format(new_node))
                    else:
                        print('(assert-soft {} :weight {})'.format(new_node,
                              str(random.randint(1, 20))))
                elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                    m_assert_id += 1
                    print(
                        '(assert (! ' +
                        format(new_node) +
                        ' :named IP_' +
                        str(m_assert_id) +
                        '))')
                    m_all_assertions.append('IP_' + str(m_assert_id))
                else:
                    print('(assert {})'.format(new_node))
                assertions -= 1

            if random.random() < 0.2:
                node1, node2 = clauses.bin_node()
                if m_test_max_smt or m_test_max_sat:
                    if random.random() < m_max_smt_rate:
                        print('(assert {})'.format(node1))
                    else:
                        print('(assert-soft {} :weight {})'.format(node1,
                              str(random.randint(1, 20))))
                    if random.random() < m_max_smt_rate:
                        print('(assert {})'.format(node2))
                    else:
                        print('(assert-soft {} :weight {})'.format(node2,
                              str(random.randint(1, 20))))
                elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                    m_assert_id += 1
                    print(
                        '(assert (! ' + format(node1) + ' :named IP_' + str(m_assert_id) + '))')
                    m_all_assertions.append('IP_' + str(m_assert_id))
                    m_assert_id += 1
                    print(
                        '(assert (! ' + format(node2) + ' :named IP_' + str(m_assert_id) + '))')
                    m_all_assertions.append('IP_' + str(m_assert_id))
                else:
                    print('(assert {})'.format(node1))
                    print('(assert {})'.format(node2))
                assertions -= 2
    # '''
    #################

    add_additional_cmds(nodes, logic)


def bool_fuzz(logic, cntsize):
    global m_assert_id, m_all_assertions
    global n_push, n_pop

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals, add_quantifiers = \
        set_logic(logic)

    nodes = Nodes(add_ints, add_reals)
    if r > 0:
        n_bvs = random.randint(1, 10)
        for _ in range(n_bvs):
            nodes.init_BV()

    if cntsize <= 20:
        assertions = 20
    else:
        assertions = random.randrange(15, cntsize)
    while assertions > 0:

        if n_push > n_pop:
            k = random.randint(1, n_push - n_pop)
            if not m_fancy_push:
                k = 1
            if random.random() < m_push_pop_rate:
                nodes.pop(k)
                n_pop += k
            elif random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k
        if n_push == n_pop:
            if random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()

        if random.random() < m_create_bool_rate:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()

        if random.random() < e:
            if m_test_string:
                nodes.string_from_string()
            elif m_test_string_lia:
                nodes.int_from_int()
                nodes.string_from_string()
            else:
                nodes.int_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.set_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bag_from_bag()

        if random.random() < f:
            if m_test_string:
                nodes.bool_from_string()
            elif m_test_string_lia:
                nodes.bool_from_int()
                nodes.bool_from_string()
            else:
                nodes.bool_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.bool_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bool_from_bag()
            if m_test_seplog and random.random() < 0.7:
                nodes.bool_from_seplog()

        if random.random() < g:
            if m_test_fp:
                nodes.new_fp()
            elif m_test_fp_lra:
                nodes.new_fp()
                nodes.new_real()
            else:
                nodes.new_real()
        if random.random() < h:
            if m_test_fp:
                nodes.fp_from_fp()
            elif m_test_fp_lra:
                nodes.fp_from_fp()
                nodes.real_from_real()
            else:
                nodes.real_from_real()
        if random.random() < m:
            if m_test_fp:
                nodes.bool_from_fp()
            elif m_test_fp_lra:
                nodes.bool_from_fp()
                nodes.bool_from_real()
            else:
                nodes.bool_from_real()

        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()
        if random.random() < add_quantifiers:
            nodes.quantifier()

        if random.random() < m_assert_or_create_new:
            new_node = nodes.bool_choice()
        else:
            new_node = nodes.bool_from_bool()

        if random.random() < 0.4:
            if m_test_max_smt or m_test_max_sat:
                if random.random() < m_max_smt_rate:
                    print('(assert {})'.format(new_node))
                else:
                    # print('(assert-soft {})'.format(new_node))
                    print('(assert-soft {} :weight {})'.format(new_node,
                          str(random.randint(1, 20))))
            elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                m_assert_id += 1
                print(
                    '(assert (! ' +
                    format(new_node) +
                    ' :named IP_' +
                    str(m_assert_id) +
                    '))')
                m_all_assertions.append('IP_' + str(m_assert_id))
            else:
                print('(assert {})'.format(new_node))
            assertions -= 1

        if random.random() < 0.05:
            if m_reset_assert and random.random() < 0.3:
                print(m_reset_cmd)

            add_additional_cmds(nodes, logic)

            print('(check-sat)')
            if m_test_smt_opt:
                print('(get-objectives)')

            if (m_test_unsat_core or m_test_proof or m_test_named_assert) and random.random(
            ) < 0.5:
                # print("(get-unsat-core)")
                tmp_num_goal = 0
                cur_all_ass = m_all_assertions
                if len(cur_all_ass) >= 2:
                    octele_cnts = list(itertools.combinations(cur_all_ass, 2))
                    random.shuffle(octele_cnts)
                    for cnt_a, cnt_b in octele_cnts:
                        print(
                            "(check-sat-assuming (" + cnt_a + " " + cnt_b + "))")
                        if m_test_unsat_core:
                            # print("(get-unsat-assumptions)")
                            print("(get-unsat-core)")
                        tmp_num_goal += 1
                        if tmp_num_goal == 5:
                            break

    add_additional_cmds(nodes, logic)


def cnf_fuzz(logic, vcratio, cntsize):
    global m_assert_id
    global m_all_assertions
    global n_push, n_pop

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals, add_quantifiers \
        = set_logic(logic)

    nodes = Nodes(add_ints, add_reals)
    if r > 0:
        n_bvs = random.randint(1, 10)
        for _ in range(n_bvs):
            nodes.init_BV()

    for _ in range(cntsize):

        if n_push > n_pop:
            k = random.randint(1, n_push - n_pop)
            if not m_fancy_push:
                k = 1
            if random.random() < m_push_pop_rate:
                nodes.pop(k)
                n_pop += k
            elif random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k
        if n_push == n_pop:
            if random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()

        if random.random() < m_create_bool_rate:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()
        if random.random() < e:
            # nodes.int_from_int()
            if m_test_string:
                nodes.string_from_string()
            elif m_test_string_lia:
                nodes.int_from_int()
                nodes.string_from_string()
            else:
                nodes.int_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.set_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bag_from_bag()

        if random.random() < f:
            # nodes.bool_from_int()
            if m_test_string:
                nodes.bool_from_string()
            elif m_test_string_lia:
                nodes.bool_from_int()
                nodes.bool_from_string()
            else:
                nodes.bool_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.bool_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bool_from_bag()
            if m_test_seplog and random.random() < 0.7:
                nodes.bool_from_seplog()
        # if random.random() < g:
        #    nodes.new_real()
        # if random.random() < h:
        #    nodes.real_from_real()
        # if random.random() < m:
        #    nodes.bool_from_real()
        if random.random() < g:
            if m_test_fp:
                nodes.new_fp()
            elif m_test_fp_lra:
                nodes.new_fp()
                nodes.new_real()
            else:
                nodes.new_real()
        if random.random() < h:
            if m_test_fp:
                nodes.fp_from_fp()
            elif m_test_fp_lra:
                nodes.fp_from_fp()
                nodes.real_from_real()
            else:
                nodes.real_from_real()
        if random.random() < m:
            if m_test_fp:
                nodes.bool_from_fp()
            elif m_test_fp_lra:
                nodes.bool_from_fp()
                nodes.bool_from_real()
            else:
                nodes.bool_from_real()

        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        # if random.random() < m_create_bool_rate:
        #    nodes.bool_from_bool()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()
        if random.random() < add_quantifiers:
            nodes.quantifier()

        if random.random() < m_assert_or_create_new:
            new_node = nodes.bool_choice()
        else:
            new_node = nodes.bool_from_bool()
        if random.random() < 0.3:
            if m_test_max_smt or m_test_max_sat:
                if random.random() < m_max_smt_rate:
                    print('(assert {})'.format(new_node))
                else:
                    # print('(assert-soft {})'.format(new_node))
                    print('(assert-soft {} :weight {})'.format(new_node,
                          str(random.randint(1, 20))))
            elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                m_assert_id += 1
                print(
                    '(assert (! ' +
                    format(new_node) +
                    ' :named IP_' +
                    str(m_assert_id) +
                    '))')
                m_all_assertions.append('IP_' + str(m_assert_id))
            else:
                print('(assert {})'.format(new_node))

        # previously, cnf_fuzz does not check-sat before the last check
        if random.random() < 0.03:
            if m_reset_assert and random.random() < 0.3:
                print(m_reset_cmd)

            add_additional_cmds(nodes, logic)

            print('(check-sat)')

    upp_b = nodes.num_bool()
    n_variables, n_clauses = Ratio(1, upp_b, vcratio)
    bank = nodes.bool_sample(n_variables)
    clauses = Clauses(bank, n_clauses)
    clauses.new_cnfs()
    add_additional_cmds(nodes, logic)


def ncnf_fuzz(logic, vcratio, cntsize):
    global m_assert_id
    global m_all_assertions
    global n_push, n_pop

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals, add_quantifiers \
        = set_logic(logic)

    nodes = Nodes(add_ints, add_reals)
    if r > 0:
        n_bvs = random.randint(1, 10)
        for _ in range(n_bvs):
            nodes.init_BV()

    for _ in range(cntsize):

        if n_push > n_pop:
            k = random.randint(1, n_push - n_pop)
            if not m_fancy_push:
                k = 1
            if random.random() < m_push_pop_rate:
                nodes.pop(k)
                n_pop += k
            elif random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k
        if n_push == n_pop:
            if random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()

        if random.random() < m_create_bool_rate:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()

        if random.random() < e:
            # nodes.int_from_int()
            if m_test_string:
                nodes.string_from_string()
            elif m_test_string_lia:
                nodes.int_from_int()
                nodes.string_from_string()
            else:
                nodes.int_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.set_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bag_from_bag()

        if random.random() < f:
            # nodes.bool_from_int()
            if m_test_string:
                nodes.bool_from_string()
            elif m_test_string_lia:
                nodes.bool_from_int()
                nodes.bool_from_string()
            else:
                nodes.bool_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.bool_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bool_from_bag()
            if m_test_seplog and random.random() < 0.7:
                nodes.bool_from_seplog()

        if random.random() < g:
            if m_test_fp:
                nodes.new_fp()
            elif m_test_fp_lra:
                nodes.new_fp()
                nodes.new_real()
            else:
                nodes.new_real()
        if random.random() < h:
            if m_test_fp:
                nodes.fp_from_fp()
            elif m_test_fp_lra:
                nodes.fp_from_fp()
                nodes.real_from_real()
            else:
                nodes.real_from_real()
        if random.random() < m:
            if m_test_fp:
                nodes.bool_from_fp()
            elif m_test_fp_lra:
                nodes.bool_from_fp()
                nodes.bool_from_real()
            else:
                nodes.bool_from_real()
        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        if random.random() < m_create_bool_rate:
            nodes.bool_from_bool()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()
        if random.random() < add_quantifiers:
            nodes.quantifier()

    upp_b = nodes.num_bool()
    n_variables, n_clauses = Ratio(1, upp_b, vcratio)
    bank = nodes.bool_sample(n_variables)
    clauses = Clauses(bank, n_clauses)
    clauses.new_dist_cnfs()

    add_additional_cmds(nodes, logic)


def CNFexp_fuzz(logic, vcratio, cntsize):
    """
    CNFexp_fuzz is a function that generates random CNF expressions based on the given logic, vcratio, and cntsize.
    It creates nodes and clauses, and then generates assertions based on the created CNF expressions.

    :param logic: The logic to be used for generating CNF expressions.
    :param vcratio: The variable to clause ratio for generating CNF expressions.
    :param cntsize: The size of the CNF expressions to be generated.
    """

    global m_assert_id, m_all_assertions
    global n_push, n_pop

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals, add_quantifiers \
        = set_logic(logic)

    nodes = Nodes(add_ints, add_reals)
    if r > 0:
        n_bvs = random.randint(1, 10)
        for _ in range(n_bvs):
            nodes.init_BV()

    for _ in range(cntsize):

        if n_push > n_pop:
            k = random.randint(1, n_push - n_pop)
            if not m_fancy_push:
                k = 1
            if random.random() < m_push_pop_rate:
                nodes.pop(k)
                n_pop += k
            elif random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k
        if n_push == n_pop:
            if random.random() < m_push_pop_rate:
                k = random.randint(1, 5)
                if not m_fancy_push:
                    k = 1
                nodes.push(k)
                n_push += k

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()

        if random.random() < m_create_bool_rate:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()

        if random.random() < e:
            # nodes.int_from_int()
            if m_test_string:
                nodes.string_from_string()
            elif m_test_string_lia:
                nodes.int_from_int()
                nodes.string_from_string()
            else:
                nodes.int_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.set_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bag_from_bag()

        if random.random() < f:
            # nodes.bool_from_int()
            if m_test_string:
                nodes.bool_from_string()
            elif m_test_string_lia:
                nodes.bool_from_int()
                nodes.bool_from_string()
            else:
                nodes.bool_from_int()

            if m_test_set_bapa and random.random() < 0.6:
                nodes.bool_from_set()
            if m_test_bag_bapa and random.random() < 0.6:
                nodes.bool_from_bag()
            if m_test_seplog and random.random() < 0.7:
                nodes.bool_from_seplog()

        if random.random() < g:
            if m_test_fp:
                nodes.new_fp()
            elif m_test_fp_lra:
                nodes.new_fp()
                nodes.new_real()
            else:
                nodes.new_real()
        if random.random() < h:
            if m_test_fp:
                nodes.fp_from_fp()
            elif m_test_fp_lra:
                nodes.fp_from_fp()
                nodes.real_from_real()
            else:
                nodes.real_from_real()
        if random.random() < m:
            if m_test_fp:
                nodes.bool_from_fp()
            elif m_test_fp_lra:
                nodes.bool_from_fp()
                nodes.bool_from_real()
            else:
                nodes.bool_from_real()

        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        if random.random() < m_create_bool_rate:
            nodes.bool_from_bool()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()
        if random.random() < add_quantifiers:
            nodes.quantifier()

    upp_b = nodes.num_bool()
    n_variables, n_clauses = Ratio(1, upp_b, vcratio)
    bank = nodes.bool_sample(n_variables)
    clauses = Clauses(bank, n_clauses)
    clauses.new_cnfs()

    assertions = random.randrange(1, 50)
    while assertions > 0:
        # try push pop here

        if random.random() < 0.5:
            new_node = clauses.cnf_choice()
        else:
            new_node = clauses.node_from_cnf()

        if random.random() < 0.6:
            if m_test_max_smt or m_test_max_sat:
                if random.random() < m_max_smt_rate:
                    print('(assert {})'.format(new_node))
                else:
                    # print('(assert-soft {})'.format(new_node))
                    print('(assert-soft {} :weight {})'.format(new_node,
                          str(random.randint(1, 20))))
            elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                m_assert_id += 1
                print(
                    '(assert (! ' +
                    format(new_node) +
                    ' :named IP_' +
                    str(m_assert_id) +
                    '))')
                m_all_assertions.append('IP_' + str(m_assert_id))
            else:
                print('(assert {})'.format(new_node))
            assertions -= 1

        if random.random() < 0.2:
            node1, node2 = clauses.bin_node()
            if m_test_max_smt or m_test_max_sat:
                if random.random() < m_max_smt_rate:
                    print('(assert {})'.format(node1))
                else:
                    # print('(assert-soft {})'.format(node1))
                    print('(assert-soft {} :weight {})'.format(node1,
                          str(random.randint(1, 20))))
                if random.random() < m_max_smt_rate:
                    print('(assert {})'.format(node2))
                else:
                    # print('(assert-soft {})'.format(node2))
                    print('(assert-soft {} :weight {})'.format(node2,
                          str(random.randint(1, 20))))
            elif m_test_unsat_core or m_test_interpolant or m_test_proof or m_test_named_assert:
                m_assert_id += 1
                print(
                    '(assert (! ' +
                    format(node1) +
                    ' :named IP_' +
                    str(m_assert_id) +
                    '))')
                m_all_assertions.append('IP_' + str(m_assert_id))
                m_assert_id += 1
                print(
                    '(assert (! ' +
                    format(node2) +
                    ' :named IP_' +
                    str(m_assert_id) +
                    '))')
                m_all_assertions.append('IP_' + str(m_assert_id))
            else:
                print('(assert {})'.format(node1))
                print('(assert {})'.format(node2))
            assertions -= 2

        if random.random() < 0.05:
            if m_reset_assert and random.random() < 0.3:
                print(m_reset_cmd)

            add_additional_cmds(nodes, logic)

            print('(check-sat)')
            if m_test_smt_opt:
                print('(get-objectives)')

            if (m_test_unsat_core or m_test_proof or m_test_named_assert) and random.random(
            ) < 0.3:  # Can we?
                if m_test_unsat_core:
                    print("(get-unsat-core)")
                tmp_num_goal = 0
                cur_all_ass = m_all_assertions
                if len(cur_all_ass) >= 2:
                    octetcents = list(itertools.combinations(cur_all_ass, 2))
                    random.shuffle(octetcents)
                    for cnt_a, cnt_b in octetcents:
                        print(
                            "(check-sat-assuming (" + cnt_a + " " + cnt_b + "))")
                        if m_test_unsat_core:
                            print("(get-unsat-core)")
                            # else: print("(get-unsat-assumptions)")
                        tmp_num_goal += 1
                        if tmp_num_goal == 5:
                            break

    add_additional_cmds(nodes, logic)


def sig_handler(signume, frame):
    sys.exit(0)


def main():
    global IntBinOp, IntNOp, m_test_proof, m_global_logic, m_set_logic, m_global_strategy, m_test_fp, \
        m_test_unsat_core, m_test_smt_opt, m_test_max_smt, m_test_seplog, m_test_string, m_test_bag_bapa, \
        m_test_bvint, m_test_fp_lra, m_test_qe, m_test_qbf, m_strict_cnf, m_test_ufc, m_test_seq, \
        m_test_string_lia, RealBinOp, RealNOp, m_test_set_bapa, m_test_set_bapa, m_test_max_sat, m_noinc_mode

    signal.signal(signal.SIGINT, sig_handler)
    signal.signal(signal.SIGTERM, sig_handler)
    # signal.signal(signal.SIGQUIT, sighandler)
    # signal.signal(signal.SIGHUP, sighandler)

    # Extend the help information for each argument in the argument parser
    parser = argparse.ArgumentParser(
        description="A script for generating SMT-LIB benchmarks based on various strategies and logics.")
    parser.add_argument(
        '--strategy',
        dest='strategy',
        default='noinc',
        type=str,
        help="Strategy for generation: noinc (non-incremental), "
        "bool, cnf, ncnf, CNFexp, strictcnf, or random (default: noinc)")
    parser.add_argument('--logic', dest='logic', default='random', type=str,
                        help="Set the logic to generate (default: random)")
    parser.add_argument(
        '--seed',
        dest='seed',
        default=None,
        help="Random seed for rand() (default: None)")
    parser.add_argument(
        '--cnfratio',
        dest='ratio',
        default=5,
        type=int,
        help="Ratio of variables to clauses in CNF generation (default: 5)")
    parser.add_argument(
        '--cntsize',
        dest='cntsize',
        default=66,
        type=int,
        help="The maximal number of assertions per query (default: 66)")
    parser.add_argument(
        '--smtopt',
        dest='smtopt',
        default=0,
        type=int,
        help="Test SMT optimization (default: 0. use 1 to enable this feature)")
    parser.add_argument(
        '--maxsmt',
        dest='maxsmt',
        default=0,
        type=int,
        help="Test Max-SMT (default: 0. use 1 to enable this feature)")
    parser.add_argument(
        '--qbf',
        dest='qbf',
        default=0,
        type=int,
        help="Test QBF solving (default: 0. use 1 to enable this feature)")
    parser.add_argument(
        '--maxsat',
        dest='maxsat',
        default=0,
        type=int,
        help="Test Max-SAT (default: 0)")
    parser.add_argument(
        '--qe',
        dest='qe',
        default=0,
        type=int,
        help="Test quantifier elimination (default: 0. use 1 to enable this feature)")
    parser.add_argument(
        '--unsat_core',
        dest='unsat_core',
        default=0,
        type=int,
        help="Test unsat_core (default: 0. use 1 to enable this feature)")
    parser.add_argument(
        '--proof',
        dest='proof',
        default=0,
        type=int,
        help="Test proof (default: 0. use 1 to enable this feature)")

    args = parser.parse_args()
    # print(args)

    total_strategies = [
        'noinc',
        'bool',
        'cnf',
        'bool',
        'ncnf',
        'noinc',
        'CNFexp',
        'strictcnf']

    m_global_logic = args.logic
    if m_global_logic == 'random':
        m_global_logic = random.choice(total_logic_options)
    else:
        if m_global_logic not in total_logic_options:
            print("; Fatal error, the logic is not supported: ", m_global_logic)
            print("; You may try the following logics: ")
            print("; ", total_logic_options)
            exit(0)

    if args.strategy == "random":
        m_global_strategy = random.choice(total_strategies)
    else:
        m_global_strategy = args.strategy

    if m_global_strategy == 'noinc':
        m_noinc_mode = True

    if not args.seed:
        random.seed(args.seed)

    # the option --qbf seems meaningless, because QBF is jus a quantified theory
    # if args.qbf == 1 and m_global_logic == "QBF": m_test_qbf = True
    if m_global_logic == "QBF":
        m_test_qbf = True

    if "IDL" in m_global_logic:
        IntBinOp = ["-"]
        IntNOp = ["-"]

    elif "RDL" in m_global_logic:
        RealBinOp = ["-"]
        RealNOp = ["-"]

    # Set (and BAPA)
    if m_global_logic == 'SET':
        m_test_set_bapa = True
    elif m_global_logic == 'STRSET':
        m_test_set_bapa = True
        m_test_string_lia = True
    elif m_global_logic == 'BAG':
        m_test_bag_bapa = True

    # String
    if m_global_logic == 'QF_S':
        m_test_string = True
    elif m_global_logic in ['QF_SLIA', 'QF_SNIA', 'QF_SLIRA', 'QF_UFSLIA', 'SEQ']:
        m_test_string_lia = True
    if m_global_logic == 'SEQ':
        m_test_seq = True

    # FP, and FP + LRA
    elif m_global_logic == 'QF_FP' or m_global_logic == 'FP':
        m_test_fp = True
    elif m_global_logic == 'QF_FPLRA' or m_global_logic == 'FPLRA':
        m_test_fp_lra = True

    elif m_global_logic == 'SEPLOG':
        m_test_seplog = True

    elif m_global_logic == 'QF_UFC' or m_global_logic == 'UFC':
        m_test_ufc = True

    elif m_global_logic == 'BVINT':
        m_test_bvint = True

    if args.maxsat == 1 and (
            m_global_logic == "BOOL" or m_global_logic == "QBF"):
        m_test_max_sat = True
    # can we use maxsat for QBF??

    if args.qe == 1:
        m_test_qe = True

    if args.unsat_core == 1:
        m_test_unsat_core = True

    if args.smtopt == 1 and m_global_logic.startswith("QF"):
        m_test_smt_opt = True

    if args.maxsmt == 1:
        m_test_max_smt = True  # can we have quantifier for maxsmt???

    if args.proof == 1:
        m_test_proof = True

    if m_global_strategy == 'bool':
        bool_fuzz(m_global_logic, args.cntsize)
    elif m_global_strategy == 'cnf':
        cnf_fuzz(m_global_logic, args.ratio, args.cntsize)
    elif m_global_strategy == 'ncnf':
        ncnf_fuzz(m_global_logic, args.ratio, args.cntsize)
    elif m_global_strategy == 'CNFexp':
        CNFexp_fuzz(m_global_logic, args.ratio, args.cntsize)
    elif m_global_strategy == 'noinc':  # non-incremental
        non_inc_fuzz(m_global_logic, args.ratio, args.cntsize)
    elif m_global_strategy == 'strictcnf':
        m_strict_cnf = True
        strict_cnf_fuz(m_global_logic, args.ratio, args.cntsize)
    else:
        non_inc_fuzz(m_global_logic, args.ratio, args.cntsize)

    print("(check-sat)")
    if m_test_unsat_core:
        print("(get-unsat-core)")
    if m_test_proof:
        print("(get-proof)")


if __name__ == "__main__":
    main()
