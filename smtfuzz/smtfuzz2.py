"""
A world-class SMT-LIB2 formula generator for comprehensive SMT solver testing.

This generator supports multiple theories, configurable complexity levels,
and sophisticated generation strategies to create diverse test cases.
"""

import random
import string
from typing import List, Dict, Set, Tuple, Optional, Union, Any
from enum import Enum
from dataclasses import dataclass, field
from abc import ABC, abstractmethod
import itertools
import math


class Theory(Enum):
    """Supported SMT-LIB2 theories."""
    QF_LIA = "QF_LIA"  # Quantifier-free linear integer arithmetic
    QF_LRA = "QF_LRA"  # Quantifier-free linear real arithmetic
    QF_NIA = "QF_NIA"  # Quantifier-free non-linear integer arithmetic
    QF_NRA = "QF_NRA"  # Quantifier-free non-linear real arithmetic
    QF_BV = "QF_BV"    # Quantifier-free bit-vectors
    QF_ABV = "QF_ABV"  # Quantifier-free arrays and bit-vectors
    QF_UF = "QF_UF"    # Quantifier-free uninterpreted functions
    QF_AUFLIA = "QF_AUFLIA"  # Arrays, uninterpreted functions, linear integer arithmetic
    QF_UFLIA = "QF_UFLIA"  # Uninterpreted functions, linear integer arithmetic
    QF_UFNIA = "QF_UFNIA"  # Uninterpreted functions, non-linear integer arithmetic
    QF_UFLRA = "QF_UFLRA"  # Uninterpreted functions, linear real arithmetic
    QF_UFNRA = "QF_UFNRA"  # Uninterpreted functions, non-linear real arithmetic
    QF_UFBV = "QF_UFBV"    # Uninterpreted functions, bit-vectors
    QF_S = "QF_S"      # Quantifier-free strings
    QF_DT = "QF_DT"    # Quantifier-free datatypes
    # Theories with quantifiers
    LIA = "LIA"        # Linear integer arithmetic
    LRA = "LRA"        # Linear real arithmetic
    NIA = "NIA"        # Non-linear integer arithmetic
    NRA = "NRA"        # Non-linear real arithmetic
    UF = "UF"          # Uninterpreted functions
    UFLIA = "UFLIA"    # Uninterpreted functions, linear integer arithmetic
    UFNIA = "UFNIA"    # Uninterpreted functions, non-linear integer arithmetic
    UFLRA = "UFLRA"    # Uninterpreted functions, linear real arithmetic
    UFNRA = "UFNRA"    # Uninterpreted functions, non-linear real arithmetic
    BV = "BV"          # Bit-vectors with quantifiers
    ABV = "ABV"        # Arrays and bit-vectors with quantifiers
    AUFLIA = "AUFLIA"  # Arrays, uninterpreted functions, linear integer arithmetic


class Sort(Enum):
    """SMT-LIB2 sorts."""
    BOOL = "Bool"
    INT = "Int"
    REAL = "Real"
    STRING = "String"
    BITVEC = "BitVec"  # Bit-vector sort


@dataclass
class GenerationConfig:
    """Configuration for formula generation."""
    theory: Theory = Theory.QF_LIA
    max_depth: int = 5
    max_variables: int = 10
    max_constants: int = 20
    max_formula_size: int = 100
    enable_quantifiers: bool = False
    max_quantifier_depth: int = 2  # Maximum nesting depth of quantifiers
    max_quantified_vars: int = 3   # Maximum number of variables per quantifier
    bitvector_width: int = 32
    array_index_sort: Sort = Sort.INT
    array_element_sort: Sort = Sort.INT
    string_max_length: int = 10
    max_uninterpreted_functions: int = 5  # Maximum number of uninterpreted functions to generate
    max_uf_arity: int = 3  # Maximum arity for uninterpreted functions
    probability_weights: Dict[str, float] = field(default_factory=lambda: {
        'variable': 0.3,
        'constant': 0.2,
        'function_app': 0.3,
        'let_binding': 0.1,
        'conditional': 0.1,
        'quantifier': 0.1  # Probability of generating quantifiers when enabled
    })
    complexity_bias: float = 0.7  # Higher values favor more complex expressions


class SMTExpression(ABC):
    """Abstract base class for SMT expressions."""
    
    @abstractmethod
    def to_smtlib(self) -> str:
        """Convert expression to SMT-LIB2 format."""
        pass
    
    @abstractmethod
    def get_sort(self) -> Sort:
        """Get the sort of this expression."""
        pass
    
    @abstractmethod
    def get_size(self) -> int:
        """Get the size (number of nodes) of this expression."""
        pass


class Variable(SMTExpression):
    """SMT variable."""
    
    def __init__(self, name: str, sort: Sort):
        self.name = name
        self.sort = sort
    
    def to_smtlib(self) -> str:
        return self.name
    
    def get_sort(self) -> Sort:
        return self.sort
    
    def get_size(self) -> int:
        return 1


class Constant(SMTExpression):
    """SMT constant."""
    
    def __init__(self, value: Union[int, float, bool, str], sort: Sort):
        self.value = value
        self.sort = sort
    
    def to_smtlib(self) -> str:
        if self.sort == Sort.BOOL:
            return "true" if self.value else "false"
        elif self.sort == Sort.INT:
            return str(self.value)
        elif self.sort == Sort.REAL:
            return f"{self.value:.6f}" if isinstance(self.value, float) else f"{self.value}.0"
        elif self.sort == Sort.STRING:
            return f'"{self.value}"'
        elif self.sort == Sort.BITVEC:
            # Format as bit-vector literal: #b... or #x... or (_ bv<value> <width>)
            return f"(_ bv{self.value} 32)"  # Using 32-bit width for simplicity
        else:
            return str(self.value)
    
    def get_sort(self) -> Sort:
        return self.sort
    
    def get_size(self) -> int:
        return 1


class FunctionApplication(SMTExpression):
    """SMT function application."""
    
    def __init__(self, function_name: str, args: List[SMTExpression], result_sort: Sort):
        self.function_name = function_name
        self.args = args
        self.result_sort = result_sort
    
    def to_smtlib(self) -> str:
        if not self.args:
            return self.function_name
        args_str = " ".join(arg.to_smtlib() for arg in self.args)
        return f"({self.function_name} {args_str})"
    
    def get_sort(self) -> Sort:
        return self.result_sort
    
    def get_size(self) -> int:
        return 1 + sum(arg.get_size() for arg in self.args)


class LetBinding(SMTExpression):
    """SMT let binding."""
    
    def __init__(self, bindings: List[Tuple[str, SMTExpression]], body: SMTExpression):
        self.bindings = bindings
        self.body = body
    
    def to_smtlib(self) -> str:
        bindings_str = " ".join(f"({var} {expr.to_smtlib()})" for var, expr in self.bindings)
        return f"(let ({bindings_str}) {self.body.to_smtlib()})"
    
    def get_sort(self) -> Sort:
        return self.body.get_sort()
    
    def get_size(self) -> int:
        return 1 + sum(expr.get_size() for _, expr in self.bindings) + self.body.get_size()


class QuantifiedExpression(SMTExpression):
    """SMT quantified expression (forall/exists)."""
    
    def __init__(self, quantifier: str, variables: List[Tuple[str, Sort]], body: SMTExpression):
        self.quantifier = quantifier  # "forall" or "exists"
        self.variables = variables    # List of (name, sort) pairs
        self.body = body
    
    def to_smtlib(self) -> str:
        vars_str = " ".join(f"({var} {self._sort_to_smtlib(sort)})" for var, sort in self.variables)
        return f"({self.quantifier} ({vars_str}) {self.body.to_smtlib()})"
    
    def get_sort(self) -> Sort:
        return Sort.BOOL  # Quantified expressions always return Bool
    
    def get_size(self) -> int:
        return 1 + self.body.get_size()
    
    def _sort_to_smtlib(self, sort: Sort) -> str:
        """Convert sort to SMT-LIB2 format."""
        if sort == Sort.BITVEC:
            return "(_ BitVec 32)"  # Using 32-bit width
        else:
            return sort.value


@dataclass
class UninterpretedFunction:
    """Represents an uninterpreted function declaration."""
    name: str
    arg_sorts: List[Sort]
    result_sort: Sort
    
    @property
    def arity(self) -> int:
        return len(self.arg_sorts)
    
    def to_declaration(self) -> str:
        """Generate SMT-LIB2 function declaration."""
        if self.arity == 0:
            return f"(declare-fun {self.name} () {self._sort_to_smtlib(self.result_sort)})"
        else:
            arg_sorts_str = " ".join(self._sort_to_smtlib(sort) for sort in self.arg_sorts)
            return f"(declare-fun {self.name} ({arg_sorts_str}) {self._sort_to_smtlib(self.result_sort)})"
    
    def _sort_to_smtlib(self, sort: Sort) -> str:
        """Convert sort to SMT-LIB2 format."""
        if sort == Sort.BITVEC:
            return "(_ BitVec 32)"  # Using 32-bit width
        else:
            return sort.value


class SMTFormulaGenerator:
    """World-class SMT-LIB2 formula generator."""
    
    def __init__(self, config: GenerationConfig, seed: Optional[int] = None):
        self.config = config
        self.random = random.Random(seed)
        self.variables: Dict[Sort, List[Variable]] = {sort: [] for sort in Sort}
        self.constants: Dict[Sort, List[Constant]] = {sort: [] for sort in Sort}
        self.let_variables: Dict[str, SMTExpression] = {}
        self.quantified_variables: Dict[str, Sort] = {}  # Track quantified variables in scope
        self.quantifier_depth = 0  # Current quantifier nesting depth
        self.uninterpreted_functions: List[UninterpretedFunction] = []
        self.formula_size = 0
        
        # Theory-specific function definitions
        self.theory_functions = self._initialize_theory_functions()
        
        # Initialize some basic variables and constants
        self._initialize_variables_and_constants()
        
        # Initialize uninterpreted functions for UF theories
        self._initialize_uninterpreted_functions()
    
    def _initialize_theory_functions(self) -> Dict[Theory, Dict[str, Dict]]:
        """Initialize function definitions for each theory."""
        return {
            Theory.QF_LIA: {
                '+': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '-': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '*': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                'div': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.INT},
                'mod': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.INT},
                'abs': {'arity': 1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '=': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.INT, Sort.INT], 'result_sort': Sort.INT},
            },
            Theory.QF_LRA: {
                '+': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '-': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '*': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '/': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
                '=': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
            },
            Theory.QF_BV: {
                'bvadd': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsub': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvmul': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvudiv': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvurem': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsdiv': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsrem': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsmod': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvand': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvor': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvxor': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvnot': {'arity': 1, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvneg': {'arity': 1, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvshl': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvlshr': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvashr': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                '=': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvult': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvule': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvugt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvuge': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvslt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsle': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsgt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsge': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.BITVEC, Sort.BITVEC], 'result_sort': Sort.BITVEC},
            },
            # UF theories combine uninterpreted functions with base theories
            Theory.QF_UF: {
                '=': {'arity': 2, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},  # Polymorphic equality
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
            },
            Theory.QF_UFLIA: {
                # Linear integer arithmetic functions (strictly linear - no *, div, mod)
                '+': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '-': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                # Note: *, div, mod are removed for linear arithmetic
                '=': {'arity': 2, 'arg_sorts': [Sort.INT], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.INT, Sort.INT], 'result_sort': Sort.INT},
            },
            Theory.QF_UFNIA: {
                # Non-linear integer arithmetic functions (same as UFLIA for now)
                '+': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '-': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '*': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                'div': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.INT},
                'mod': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.INT},
                'abs': {'arity': 1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '=': {'arity': 2, 'arg_sorts': [Sort.INT], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.INT, Sort.INT], 'result_sort': Sort.INT},
            },
            Theory.QF_UFLRA: {
                # Linear real arithmetic functions (strictly linear - no *, /)
                '+': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '-': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                # Note: *, / are removed for linear arithmetic
                '=': {'arity': 2, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
            },
            Theory.QF_UFNRA: {
                # Non-linear real arithmetic functions (same as UFLRA for now)
                '+': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '-': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '*': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '/': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
                '=': {'arity': 2, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
            },
            Theory.QF_UFBV: {
                # Bit-vector functions
                'bvadd': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsub': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvmul': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvudiv': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvurem': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvand': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvor': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvxor': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvnot': {'arity': 1, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvneg': {'arity': 1, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvshl': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvlshr': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvashr': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                '=': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvult': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvule': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvugt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvuge': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvslt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsle': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsgt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsge': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.BITVEC, Sort.BITVEC], 'result_sort': Sort.BITVEC},
            },
            # Quantified theories (same functions as QF versions but with quantifiers enabled)
            Theory.LIA: {
                '+': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '-': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                # Note: * removed for linear arithmetic
                '=': {'arity': 2, 'arg_sorts': [Sort.INT], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.INT, Sort.INT], 'result_sort': Sort.INT},
            },
            Theory.LRA: {
                '+': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '-': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                # Note: * removed for linear arithmetic
                '=': {'arity': 2, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
            },
            Theory.NIA: {
                '+': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '-': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '*': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                'div': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.INT},
                'mod': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.INT},
                'abs': {'arity': 1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '=': {'arity': 2, 'arg_sorts': [Sort.INT], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.INT, Sort.INT], 'result_sort': Sort.INT},
            },
            Theory.NRA: {
                '+': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '-': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '*': {'arity': -1, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.REAL},
                '/': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
                '=': {'arity': 2, 'arg_sorts': [Sort.REAL], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.REAL, Sort.REAL], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.REAL, Sort.REAL], 'result_sort': Sort.REAL},
            },
            Theory.UF: {
                '=': {'arity': 2, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},  # Polymorphic equality
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
            },
            Theory.UFLIA: {
                '+': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '-': {'arity': -1, 'arg_sorts': [Sort.INT], 'result_sort': Sort.INT},
                '=': {'arity': 2, 'arg_sorts': [Sort.INT], 'result_sort': Sort.BOOL},
                '<': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '<=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                '>=': {'arity': 2, 'arg_sorts': [Sort.INT, Sort.INT], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.INT, Sort.INT], 'result_sort': Sort.INT},
            },
            Theory.BV: {
                # Bit-vector functions (same as QF_BV but with quantifiers enabled)
                'bvadd': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsub': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvmul': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvudiv': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvurem': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsdiv': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsrem': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvsmod': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvand': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvor': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvxor': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvnot': {'arity': 1, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvneg': {'arity': 1, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvshl': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvlshr': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                'bvashr': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BITVEC},
                '=': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvult': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvule': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvugt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvuge': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvslt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsle': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsgt': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'bvsge': {'arity': 2, 'arg_sorts': [Sort.BITVEC], 'result_sort': Sort.BOOL},
                'and': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'or': {'arity': -1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                'not': {'arity': 1, 'arg_sorts': [Sort.BOOL], 'result_sort': Sort.BOOL},
                '=>': {'arity': 2, 'arg_sorts': [Sort.BOOL, Sort.BOOL], 'result_sort': Sort.BOOL},
                'ite': {'arity': 3, 'arg_sorts': [Sort.BOOL, Sort.BITVEC, Sort.BITVEC], 'result_sort': Sort.BITVEC},
            }
        }
    
    def _initialize_variables_and_constants(self):
        """Initialize basic variables and constants."""
        # Create variables based on theory
        int_theories = [Theory.QF_LIA, Theory.QF_NIA, Theory.QF_AUFLIA, Theory.QF_UFLIA, Theory.QF_UFNIA,
                       Theory.LIA, Theory.NIA, Theory.UFLIA]
        real_theories = [Theory.QF_LRA, Theory.QF_NRA, Theory.QF_UFLRA, Theory.QF_UFNRA,
                        Theory.LRA, Theory.NRA, Theory.UFLRA]
        bv_theories = [Theory.QF_BV, Theory.QF_ABV, Theory.QF_UFBV, Theory.BV, Theory.ABV]
        
        if self.config.theory in int_theories:
            for i in range(min(5, self.config.max_variables)):
                var = Variable(f"x{i}", Sort.INT)
                self.variables[Sort.INT].append(var)
        
        if self.config.theory in real_theories:
            for i in range(min(5, self.config.max_variables)):
                var = Variable(f"r{i}", Sort.REAL)
                self.variables[Sort.REAL].append(var)
        
        if self.config.theory in bv_theories:
            for i in range(min(5, self.config.max_variables)):
                var = Variable(f"bv{i}", Sort.BITVEC)
                self.variables[Sort.BITVEC].append(var)
        
        # Create constants
        if self.config.theory in int_theories:
            for _ in range(min(10, self.config.max_constants)):
                const = Constant(self.random.randint(-100, 100), Sort.INT)
                self.constants[Sort.INT].append(const)
        
        if self.config.theory in real_theories:
            for _ in range(min(10, self.config.max_constants)):
                const = Constant(self.random.uniform(-100.0, 100.0), Sort.REAL)
                self.constants[Sort.REAL].append(const)
        
        if self.config.theory in bv_theories:
            for _ in range(min(10, self.config.max_constants)):
                # Generate bit-vector constants with proper SMT-LIB2 format
                value = self.random.randint(0, (2 ** self.config.bitvector_width) - 1)
                const = Constant(value, Sort.BITVEC)
                self.constants[Sort.BITVEC].append(const)
        
        # Boolean constants
        self.constants[Sort.BOOL].extend([
            Constant(True, Sort.BOOL),
            Constant(False, Sort.BOOL)
        ])
    
    def _initialize_uninterpreted_functions(self):
        """Initialize uninterpreted functions for UF theories."""
        uf_theories = [Theory.QF_UF, Theory.QF_UFLIA, Theory.QF_UFNIA, Theory.QF_UFLRA, Theory.QF_UFNRA, Theory.QF_UFBV,
                      Theory.UF, Theory.UFLIA]
        
        if self.config.theory not in uf_theories:
            return
        
        # Determine available sorts based on theory
        available_sorts = [Sort.BOOL]  # All UF theories support Bool
        
        if self.config.theory in [Theory.QF_UFLIA, Theory.QF_UFNIA, Theory.UFLIA]:
            available_sorts.append(Sort.INT)
        elif self.config.theory in [Theory.QF_UFLRA, Theory.QF_UFNRA]:
            available_sorts.append(Sort.REAL)
        elif self.config.theory == Theory.QF_UFBV:
            available_sorts.append(Sort.BITVEC)
        
        # Generate uninterpreted functions
        for i in range(self.config.max_uninterpreted_functions):
            # Choose function name
            func_name = f"f{i}"
            
            # Choose arity (0 to max_uf_arity)
            arity = self.random.randint(0, self.config.max_uf_arity)
            
            # Choose argument sorts
            arg_sorts = []
            for _ in range(arity):
                arg_sort = self.random.choice(available_sorts)
                arg_sorts.append(arg_sort)
            
            # Choose result sort
            result_sort = self.random.choice(available_sorts)
            
            # Create uninterpreted function
            uf = UninterpretedFunction(func_name, arg_sorts, result_sort)
            self.uninterpreted_functions.append(uf)
    
    def generate_expression(self, target_sort: Sort, depth: int = 0) -> SMTExpression:
        """Generate a random SMT expression of the given sort."""
        if depth >= self.config.max_depth or self.formula_size >= self.config.max_formula_size:
            return self._generate_terminal(target_sort)
        
        # Choose expression type based on weights and complexity bias
        choices = []
        weights = []
        
        # Terminal expressions (variables and constants)
        if self.variables[target_sort] or self.constants[target_sort]:
            choices.append('terminal')
            weights.append(self.config.probability_weights.get('variable', 0.3) + 
                          self.config.probability_weights.get('constant', 0.2))
        
        # Function applications
        if self._can_generate_function_app(target_sort):
            choices.append('function_app')
            weights.append(self.config.probability_weights.get('function_app', 0.3) * 
                          (self.config.complexity_bias ** depth))
        
        # Let bindings
        if depth < self.config.max_depth - 1:
            choices.append('let_binding')
            weights.append(self.config.probability_weights.get('let_binding', 0.1) * 
                          (self.config.complexity_bias ** depth))
        
        # Conditional expressions (for non-boolean sorts)
        if target_sort != Sort.BOOL and depth < self.config.max_depth - 1:
            choices.append('conditional')
            weights.append(self.config.probability_weights.get('conditional', 0.1) * 
                          (self.config.complexity_bias ** depth))
        
        # Quantified expressions (only for Bool sort and when enabled)
        if (target_sort == Sort.BOOL and self.config.enable_quantifiers and 
            self.quantifier_depth < self.config.max_quantifier_depth and
            depth < self.config.max_depth - 1 and
            self._supports_quantifiers()):
            choices.append('quantifier')
            weights.append(self.config.probability_weights.get('quantifier', 0.1) * 
                          (self.config.complexity_bias ** depth))
        
        if not choices:
            return self._generate_terminal(target_sort)
        
        choice = self.random.choices(choices, weights=weights)[0]
        
        if choice == 'terminal':
            return self._generate_terminal(target_sort)
        elif choice == 'function_app':
            return self._generate_function_application(target_sort, depth)
        elif choice == 'let_binding':
            return self._generate_let_binding(target_sort, depth)
        elif choice == 'conditional':
            return self._generate_conditional(target_sort, depth)
        elif choice == 'quantifier':
            return self._generate_quantified_expression(depth)
        else:
            return self._generate_terminal(target_sort)
    
    def _generate_terminal(self, target_sort: Sort) -> SMTExpression:
        """Generate a terminal expression (variable or constant)."""
        choices = []
        
        # Add regular variables
        if self.variables[target_sort]:
            choices.extend(self.variables[target_sort])
        
        # Add quantified variables of the target sort
        for var_name, var_sort in self.quantified_variables.items():
            if var_sort == target_sort:
                choices.append(Variable(var_name, var_sort))
        
        if self.constants[target_sort]:
            choices.extend(self.constants[target_sort])
        
        if choices:
            expr = self.random.choice(choices)
            self.formula_size += 1
            return expr
        
        # Fallback: create a new constant
        if target_sort == Sort.INT:
            const = Constant(self.random.randint(-10, 10), Sort.INT)
        elif target_sort == Sort.REAL:
            const = Constant(self.random.uniform(-10.0, 10.0), Sort.REAL)
        elif target_sort == Sort.BOOL:
            const = Constant(self.random.choice([True, False]), Sort.BOOL)
        elif target_sort == Sort.BITVEC:
            const = Constant(self.random.randint(0, (2 ** self.config.bitvector_width) - 1), Sort.BITVEC)
        else:
            const = Constant(0, Sort.INT)  # Fallback
        
        self.formula_size += 1
        return const
    
    def _can_generate_function_app(self, target_sort: Sort) -> bool:
        """Check if we can generate a function application for the target sort."""
        # Check theory functions
        theory_funcs = self.theory_functions.get(self.config.theory, {})
        if any(func_info['result_sort'] == target_sort for func_info in theory_funcs.values()):
            return True
        
        # Check uninterpreted functions
        return any(uf.result_sort == target_sort for uf in self.uninterpreted_functions)
    
    def _generate_function_application(self, target_sort: Sort, depth: int) -> SMTExpression:
        """Generate a function application."""
        # Collect all applicable functions (theory + uninterpreted)
        applicable_choices = []
        
        # Theory functions
        theory_funcs = self.theory_functions.get(self.config.theory, {})
        for name, info in theory_funcs.items():
            if info['result_sort'] == target_sort:
                applicable_choices.append(('theory', name, info))
        
        # Uninterpreted functions
        for uf in self.uninterpreted_functions:
            if uf.result_sort == target_sort:
                applicable_choices.append(('uf', uf.name, uf))
        
        if not applicable_choices:
            return self._generate_terminal(target_sort)
        
        # Choose a function
        choice_type, func_name, func_info = self.random.choice(applicable_choices)
        
        # Generate arguments
        args = []
        
        if choice_type == 'theory':
            # Handle theory functions
            arity = func_info['arity']
            arg_sorts = func_info['arg_sorts']
            
            if arity == -1:  # Variable arity
                num_args = self.random.randint(2, min(4, self.config.max_depth - depth + 1))
                arg_sort = arg_sorts[0]
                for _ in range(num_args):
                    arg = self.generate_expression(arg_sort, depth + 1)
                    args.append(arg)
            else:  # Fixed arity
                for i in range(arity):
                    arg_sort = arg_sorts[i] if i < len(arg_sorts) else arg_sorts[-1]
                    arg = self.generate_expression(arg_sort, depth + 1)
                    args.append(arg)
        
        else:  # choice_type == 'uf'
            # Handle uninterpreted functions
            uf = func_info  # func_info is actually the UninterpretedFunction object
            for arg_sort in uf.arg_sorts:
                arg = self.generate_expression(arg_sort, depth + 1)
                args.append(arg)
        
        self.formula_size += 1
        return FunctionApplication(func_name, args, target_sort)
    
    def _generate_let_binding(self, target_sort: Sort, depth: int) -> SMTExpression:
        """Generate a let binding."""
        num_bindings = self.random.randint(1, 3)
        bindings = []
        
        for i in range(num_bindings):
            var_name = f"let_var_{len(self.let_variables)}_{i}"
            # Choose a random sort for the binding based on theory
            available_sorts = [Sort.BOOL]
            int_theories = [Theory.QF_LIA, Theory.QF_NIA, Theory.QF_AUFLIA, Theory.QF_UFLIA, Theory.QF_UFNIA,
                           Theory.LIA, Theory.NIA, Theory.UFLIA]
            real_theories = [Theory.QF_LRA, Theory.QF_NRA, Theory.QF_UFLRA, Theory.QF_UFNRA,
                            Theory.LRA, Theory.NRA]
            bv_theories = [Theory.QF_BV, Theory.QF_ABV, Theory.QF_UFBV, Theory.BV, Theory.ABV]
            
            if self.config.theory in int_theories:
                available_sorts.append(Sort.INT)
            if self.config.theory in real_theories:
                available_sorts.append(Sort.REAL)
            if self.config.theory in bv_theories:
                available_sorts.append(Sort.BITVEC)
            
            binding_sort = self.random.choice(available_sorts)
            binding_expr = self.generate_expression(binding_sort, depth + 1)
            bindings.append((var_name, binding_expr))
            
            # Add to let variables for potential use in body
            self.let_variables[var_name] = binding_expr
        
        # Generate body
        body = self.generate_expression(target_sort, depth + 1)
        
        # Clean up let variables
        for var_name, _ in bindings:
            del self.let_variables[var_name]
        
        self.formula_size += 1
        return LetBinding(bindings, body)
    
    def _generate_conditional(self, target_sort: Sort, depth: int) -> SMTExpression:
        """Generate a conditional (ite) expression."""
        condition = self.generate_expression(Sort.BOOL, depth + 1)
        then_expr = self.generate_expression(target_sort, depth + 1)
        else_expr = self.generate_expression(target_sort, depth + 1)
        
        self.formula_size += 1
        return FunctionApplication("ite", [condition, then_expr, else_expr], target_sort)
    
    def _supports_quantifiers(self) -> bool:
        """Check if the current theory supports quantifiers."""
        quantified_theories = [Theory.LIA, Theory.LRA, Theory.NIA, Theory.NRA, Theory.UF, 
                              Theory.UFLIA, Theory.BV, Theory.ABV, Theory.AUFLIA]
        return self.config.theory in quantified_theories
    
    def _generate_quantified_expression(self, depth: int) -> QuantifiedExpression:
        """Generate a quantified expression (forall/exists)."""
        # Choose quantifier type
        quantifier = self.random.choice(["forall", "exists"])
        
        # Generate quantified variables
        num_vars = self.random.randint(1, self.config.max_quantified_vars)
        variables = []
        
        # Determine available sorts for quantified variables based on theory
        available_sorts = [Sort.BOOL]
        if self.config.theory in [Theory.LIA, Theory.NIA, Theory.UFLIA]:
            available_sorts.append(Sort.INT)
        if self.config.theory in [Theory.LRA, Theory.NRA]:
            available_sorts.append(Sort.REAL)
        if self.config.theory in [Theory.BV, Theory.ABV]:
            available_sorts.append(Sort.BITVEC)
        
        # Generate unique variable names and sorts
        for i in range(num_vars):
            var_name = f"q{self.quantifier_depth}_{i}"
            var_sort = self.random.choice(available_sorts)
            variables.append((var_name, var_sort))
            
            # Add to quantified variables scope
            self.quantified_variables[var_name] = var_sort
        
        # Increase quantifier depth
        self.quantifier_depth += 1
        
        # Generate body (must be Bool)
        body = self.generate_expression(Sort.BOOL, depth + 1)
        
        # Decrease quantifier depth and clean up variables
        self.quantifier_depth -= 1
        for var_name, _ in variables:
            del self.quantified_variables[var_name]
        
        self.formula_size += 1
        return QuantifiedExpression(quantifier, variables, body)
    
    def generate_formula(self, num_assertions: int = 1) -> str:
        """Generate a complete SMT-LIB2 formula with multiple assertions."""
        self.formula_size = 0
        
        # Build the complete SMT-LIB2 script
        script_parts = []
        
        # Set logic
        script_parts.append(f"(set-logic {self.config.theory.value})")
        
        # Declare uninterpreted functions
        for uf in self.uninterpreted_functions:
            script_parts.append(uf.to_declaration())
        
        # Declare variables
        declared_vars = set()
        for sort, vars_list in self.variables.items():
            for var in vars_list:
                if var.name not in declared_vars:
                    if sort == Sort.BITVEC:
                        script_parts.append(f"(declare-fun {var.name} () (_ BitVec {self.config.bitvector_width}))")
                    else:
                        script_parts.append(f"(declare-fun {var.name} () {sort.value})")
                    declared_vars.add(var.name)
        
        # Generate multiple assertions
        for i in range(num_assertions):
            assertion_expr = self.generate_expression(Sort.BOOL)
            script_parts.append(f"(assert {assertion_expr.to_smtlib()})")
        
        # Check satisfiability
        script_parts.append("(check-sat)")
        
        return "\n".join(script_parts)
    
    def generate_multiple_formulas(self, count: int, num_assertions: int = 1) -> List[str]:
        """Generate multiple formulas."""
        formulas = []
        for _ in range(count):
            # Reset state for each formula
            self.formula_size = 0
            self.let_variables.clear()
            formula = self.generate_formula(num_assertions)
            formulas.append(formula)
        return formulas


class SMTFuzzTester:
    """Advanced SMT fuzzing test suite."""
    
    def __init__(self, seed: Optional[int] = None):
        self.random = random.Random(seed)
        self.generators: Dict[Theory, SMTFormulaGenerator] = {}
        self.generated_formulas: List[str] = []
    
    def create_generator(self, theory: Theory, **config_kwargs) -> SMTFormulaGenerator:
        """Create a generator for a specific theory."""
        config = GenerationConfig(theory=theory, **config_kwargs)
        generator = SMTFormulaGenerator(config, self.random.randint(0, 2**32))
        self.generators[theory] = generator
        return generator
    
    def generate_test_suite(self, 
                          theories: List[Theory], 
                          formulas_per_theory: int = 10,
                          complexity_levels: List[int] = [3, 5, 7]) -> Dict[Theory, List[str]]:
        """Generate a comprehensive test suite."""
        test_suite = {}
        
        for theory in theories:
            formulas = []
            
            for complexity in complexity_levels:
                generator = self.create_generator(
                    theory,
                    max_depth=complexity,
                    max_formula_size=complexity * 20
                )
                
                theory_formulas = generator.generate_multiple_formulas(
                    formulas_per_theory // len(complexity_levels)
                )
                formulas.extend(theory_formulas)
            
            test_suite[theory] = formulas
        
        return test_suite
    
    def generate_stress_test(self, theory: Theory, count: int = 100) -> List[str]:
        """Generate stress test formulas with high complexity."""
        generator = self.create_generator(
            theory,
            max_depth=10,
            max_formula_size=200,
            max_variables=20,
            complexity_bias=0.8
        )
        
        return generator.generate_multiple_formulas(count)
    
    def generate_pattern_based_formulas(self, theory: Theory, patterns: List[str], count: int = 5) -> List[str]:
        """Generate formulas based on specific patterns."""
        formulas = []
        generator = self.create_generator(theory, max_depth=6, complexity_bias=0.85)
        
        for pattern in patterns:
            pattern_formulas = []
            for _ in range(count):
                if pattern == "nested_arithmetic":
                    # Generate deeply nested arithmetic expressions
                    config = GenerationConfig(
                        theory=theory,
                        max_depth=8,
                        probability_weights={
                            'variable': 0.1,
                            'constant': 0.1,
                            'function_app': 0.7,
                            'let_binding': 0.05,
                            'conditional': 0.05
                        }
                    )
                elif pattern == "boolean_heavy":
                    # Generate boolean-heavy formulas
                    config = GenerationConfig(
                        theory=theory,
                        max_depth=6,
                        probability_weights={
                            'variable': 0.2,
                            'constant': 0.1,
                            'function_app': 0.6,
                            'let_binding': 0.05,
                            'conditional': 0.05
                        }
                    )
                elif pattern == "let_intensive":
                    # Generate formulas with many let bindings
                    config = GenerationConfig(
                        theory=theory,
                        max_depth=5,
                        probability_weights={
                            'variable': 0.15,
                            'constant': 0.1,
                            'function_app': 0.35,
                            'let_binding': 0.3,
                            'conditional': 0.1
                        }
                    )
                else:
                    config = GenerationConfig(theory=theory)
                
                pattern_gen = SMTFormulaGenerator(config, self.random.randint(0, 2**32))
                formula = pattern_gen.generate_formula()
                pattern_formulas.append(formula)
            
            formulas.extend(pattern_formulas)
        
        return formulas
    
    def save_formulas_to_files(self, formulas: List[str], base_filename: str = "generated_formula"):
        """Save generated formulas to individual SMT-LIB2 files."""
        import os
        os.makedirs("generated_formulas", exist_ok=True)
        
        for i, formula in enumerate(formulas):
            filename = f"generated_formulas/{base_filename}_{i+1:03d}.smt2"
            with open(filename, 'w') as f:
                f.write(formula)
        
        print(f"Saved {len(formulas)} formulas to generated_formulas/ directory")
    
    def analyze_formula_complexity(self, formulas: List[str]) -> Dict[str, Any]:
        """Analyze the complexity characteristics of generated formulas."""
        stats = {
            'total_formulas': len(formulas),
            'avg_length': 0,
            'max_length': 0,
            'min_length': float('inf'),
            'function_counts': {},
            'variable_counts': {},
        }
        
        total_length = 0
        for formula in formulas:
            length = len(formula)
            total_length += length
            stats['max_length'] = max(stats['max_length'], length)
            stats['min_length'] = min(stats['min_length'], length)
            
            # Count function occurrences
            for func in ['and', 'or', 'not', '+', '-', '*', '=', '<', '<=', '>', '>=']:
                count = formula.count(f'({func} ')
                stats['function_counts'][func] = stats['function_counts'].get(func, 0) + count
        
        stats['avg_length'] = total_length / len(formulas) if formulas else 0
        stats['min_length'] = stats['min_length'] if stats['min_length'] != float('inf') else 0
        
        return stats


def cli_interface():
    """Simplified CLI interface - generates one SMT-LIB2 formula per run."""
    import argparse
    
    parser = argparse.ArgumentParser(description="SMT-LIB2 Formula Generator")
    parser.add_argument('--theory', choices=[t.value for t in Theory], default='QF_LIA',
                       help='SMT theory (default: QF_LIA)')
    parser.add_argument('--depth', type=int, default=5,
                       help='Maximum expression depth (default: 5)')
    parser.add_argument('--assertions', type=int, default=3,
                       help='Number of assertions (default: 3)')
    parser.add_argument('--complexity', type=float, default=0.7,
                       help='Complexity bias 0.0-1.0 (default: 0.7)')
    parser.add_argument('--enable-quantifiers', action='store_true',
                       help='Enable quantifier generation (for non-QF theories)')
    parser.add_argument('--max-quantifier-depth', type=int, default=2,
                       help='Maximum quantifier nesting depth (default: 2)')
    parser.add_argument('--max-quantified-vars', type=int, default=3,
                       help='Maximum variables per quantifier (default: 3)')
    parser.add_argument('--seed', type=int, help='Random seed')
    
    args = parser.parse_args()
    
    # Create generator
    config = GenerationConfig(
        theory=Theory(args.theory),
        max_depth=args.depth,
        complexity_bias=args.complexity,
        enable_quantifiers=args.enable_quantifiers,
        max_quantifier_depth=args.max_quantifier_depth,
        max_quantified_vars=args.max_quantified_vars
    )
    generator = SMTFormulaGenerator(config, args.seed)
    
    # Generate and output one formula
    formula = generator.generate_formula(args.assertions)
    print(formula)


if __name__ == "__main__":
    cli_interface()


