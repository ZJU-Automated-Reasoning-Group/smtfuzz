# coding: utf-8
"""
Skeletal Approximation Enumeration (SAE) for SMT Solver Testing

This module implements the SAE strategy described in the paper:
"Skeletal Approximation Enumeration for SMT Solver Testing"

SAE is a novel lightweight and general testing technique for all first-order
theories. It leverages logical approximations as the meta-morphic relation.
"""

import argparse
import random
import itertools
from typing import List, Dict, Set, Tuple, Optional
from z3 import *


class SAEMutator:
    """
    Skeletal Approximation Enumeration mutator for SMT formulas.
    
    This class implements the SAE strategy which:
    1. Transforms seed formulas into CNF
    2. Enumerates approximations of literals
    3. Generates mutants that preserve metamorphic relations
    """
    
    def __init__(self):
        self.logic = None
        self.success = False
        self.formula = None
        self.cnf_formula = None
        self.assertions = []
        self.literals = []  # All literals in the formula
        self.atoms = []     # All atomic predicates
        self.vars = []      # All variables
        self.approximation_rules = {}
        
    def init_from_file(self, seed_file: str) -> bool:
        """
        Initialize the mutator from an SMT-LIB2 file.
        
        Args:
            seed_file: Path to the SMT-LIB2 seed file
            
        Returns:
            True if initialization successful, False otherwise
        """
        try:
            with open(seed_file, 'r') as f:
                script = f.read()
            
            self.assertions = parse_smt2_string(script)
            if len(self.assertions) < 1:
                return False
            elif len(self.assertions) == 1:
                self.formula = self.assertions[0]
            else:
                self.formula = And(self.assertions)
                
            # Convert to CNF for skeletal approximation
            self.cnf_formula = self._to_cnf(self.formula)
            
            # Extract literals and atoms
            self.literals = self._extract_literals(self.cnf_formula)
            self.atoms = self._extract_atoms(self.cnf_formula)
            self.vars = self._get_vars(self.formula)
            
            # Initialize approximation rules based on theory
            self._init_approximation_rules()
            
            self.success = True
            return True
            
        except Exception as e:
            print(f"Error initializing from file {seed_file}: {e}")
            return False
    
    def _to_cnf(self, formula):
        """Convert formula to CNF using Z3 tactics."""
        try:
            goal = Goal()
            goal.add(formula)
            cnf_tactic = Then('simplify', 'tseitin-cnf')
            cnf_result = cnf_tactic(goal)
            if len(cnf_result) > 0:
                return cnf_result[0].as_expr()
            return formula
        except:
            return formula
    
    def _extract_literals(self, formula) -> List:
        """Extract all literals from the CNF formula."""
        literals = []
        
        def collect_literals(expr):
            if is_not(expr):
                literals.append(expr)
            elif is_and(expr) or is_or(expr):
                for child in expr.children():
                    collect_literals(child)
            elif is_bool(expr):
                literals.append(expr)
        
        collect_literals(formula)
        return list(set(literals))
    
    def _extract_atoms(self, formula) -> List:
        """Extract all atomic predicates from the formula."""
        atoms = set()
        
        def collect_atoms(expr):
            if is_not(expr):
                atoms.add(expr.arg(0))
            elif is_and(expr) or is_or(expr):
                for child in expr.children():
                    collect_atoms(child)
            elif is_bool(expr) and not (is_true(expr) or is_false(expr)):
                atoms.add(expr)
        
        collect_atoms(formula)
        return list(atoms)
    
    def _get_vars(self, expr) -> List:
        """Get all variables in the expression."""
        vars_set = set()
        stack = [expr]
        
        while stack:
            e = stack.pop()
            if is_app(e):
                if e.num_args() == 0 and e.decl().kind() == Z3_OP_UNINTERPRETED:
                    vars_set.add(e)
                else:
                    stack.extend(e.children())
        
        return list(vars_set)
    
    def _init_approximation_rules(self):
        """Initialize approximation rules based on the theory."""
        # Integer theory approximation rules
        self.approximation_rules['int'] = {
            '<=': self._approximate_leq,
            '<': self._approximate_lt,
            '>=': self._approximate_geq,
            '>': self._approximate_gt,
            '=': self._approximate_eq,
            '+': self._approximate_add,
            '-': self._approximate_sub,
            '*': self._approximate_mul
        }
        
        # Real theory approximation rules
        self.approximation_rules['real'] = {
            '<=': self._approximate_leq,
            '<': self._approximate_lt,
            '>=': self._approximate_geq,
            '>': self._approximate_gt,
            '=': self._approximate_eq,
            '+': self._approximate_add,
            '-': self._approximate_sub,
            '*': self._approximate_mul
        }
        
        # Boolean theory approximation rules
        self.approximation_rules['bool'] = {
            'and': self._approximate_and,
            'or': self._approximate_or,
            'not': self._approximate_not,
            '=>': self._approximate_implies
        }
    
    def _approximate_leq(self, literal):
        """Generate over/under approximations for <= literals."""
        if is_app(literal) and literal.decl().name() == '<=':
            lhs, rhs = literal.arg(0), literal.arg(1)
            
            # Over-approximation: x <= y becomes x < y + 1 (for integers)
            over_approx = lhs < rhs + 1 if self._is_int_expr(lhs) else lhs <= rhs
            
            # Under-approximation: x <= y becomes x < y
            under_approx = lhs < rhs
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_lt(self, literal):
        """Generate over/under approximations for < literals."""
        if is_app(literal) and literal.decl().name() == '<':
            lhs, rhs = literal.arg(0), literal.arg(1)
            
            # Over-approximation: x < y becomes x <= y
            over_approx = lhs <= rhs
            
            # Under-approximation: x < y becomes x <= y - 1 (for integers)
            under_approx = lhs <= rhs - 1 if self._is_int_expr(lhs) else lhs < rhs
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_geq(self, literal):
        """Generate over/under approximations for >= literals."""
        if is_app(literal) and literal.decl().name() == '>=':
            lhs, rhs = literal.arg(0), literal.arg(1)
            
            # Over-approximation: x >= y becomes x > y - 1 (for integers)
            over_approx = lhs > rhs - 1 if self._is_int_expr(lhs) else lhs >= rhs
            
            # Under-approximation: x >= y becomes x > y
            under_approx = lhs > rhs
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_gt(self, literal):
        """Generate over/under approximations for > literals."""
        if is_app(literal) and literal.decl().name() == '>':
            lhs, rhs = literal.arg(0), literal.arg(1)
            
            # Over-approximation: x > y becomes x >= y
            over_approx = lhs >= rhs
            
            # Under-approximation: x > y becomes x >= y + 1 (for integers)
            under_approx = lhs >= rhs + 1 if self._is_int_expr(lhs) else lhs > rhs
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_eq(self, literal):
        """Generate over/under approximations for = literals."""
        if is_app(literal) and literal.decl().name() == '=':
            lhs, rhs = literal.arg(0), literal.arg(1)
            
            # Over-approximation: x = y becomes True (always satisfiable)
            over_approx = BoolVal(True)
            
            # Under-approximation: x = y becomes x = y (no change)
            under_approx = literal
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_add(self, literal):
        """Generate approximations for addition operations."""
        # For arithmetic operations, we can approximate by simplifying
        return literal, literal
    
    def _approximate_sub(self, literal):
        """Generate approximations for subtraction operations."""
        return literal, literal
    
    def _approximate_mul(self, literal):
        """Generate approximations for multiplication operations."""
        return literal, literal
    
    def _approximate_and(self, literal):
        """Generate over/under approximations for AND literals."""
        if is_and(literal):
            children = literal.children()
            
            # Over-approximation: (and A B) becomes A or B (weaker constraint)
            over_approx = Or(children) if len(children) > 1 else children[0]
            
            # Under-approximation: (and A B) stays the same
            under_approx = literal
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_or(self, literal):
        """Generate over/under approximations for OR literals."""
        if is_or(literal):
            children = literal.children()
            
            # Over-approximation: (or A B) stays the same
            over_approx = literal
            
            # Under-approximation: (or A B) becomes (and A B) (stronger constraint)
            under_approx = And(children) if len(children) > 1 else children[0]
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_not(self, literal):
        """Generate approximations for NOT literals."""
        if is_not(literal):
            # For negation, we can try to eliminate it in approximations
            inner = literal.arg(0)
            
            # Over-approximation: not A becomes True
            over_approx = BoolVal(True)
            
            # Under-approximation: not A stays the same
            under_approx = literal
            
            return over_approx, under_approx
        return literal, literal
    
    def _approximate_implies(self, literal):
        """Generate approximations for implication literals."""
        if is_app(literal) and literal.decl().name() == '=>':
            lhs, rhs = literal.arg(0), literal.arg(1)
            
            # Over-approximation: A => B becomes True
            over_approx = BoolVal(True)
            
            # Under-approximation: A => B becomes (not A) or B
            under_approx = Or(Not(lhs), rhs)
            
            return over_approx, under_approx
        return literal, literal
    
    def _is_int_expr(self, expr) -> bool:
        """Check if expression is of integer type."""
        try:
            return expr.sort().kind() == Z3_INT_SORT
        except:
            return False
    
    def generate_skeletal_approximation(self, approximation_type='over') -> str:
        """
        Generate a skeletal approximation of the formula.
        
        Args:
            approximation_type: 'over' for over-approximation, 'under' for under-approximation
            
        Returns:
            SMT-LIB2 string of the approximated formula
        """
        if not self.success:
            return ""
        
        approximated_literals = []
        
        for literal in self.literals:
            over_approx, under_approx = self._get_approximation(literal)
            
            if approximation_type == 'over':
                approximated_literals.append(over_approx)
            else:
                approximated_literals.append(under_approx)
        
        # Reconstruct the formula with approximated literals
        if len(approximated_literals) == 1:
            approximated_formula = approximated_literals[0]
        else:
            approximated_formula = And(approximated_literals)
        
        # Convert to SMT-LIB2 format
        solver = Solver()
        solver.add(approximated_formula)
        return solver.to_smt2()
    
    def _get_approximation(self, literal):
        """Get over and under approximations for a literal."""
        if is_app(literal):
            op_name = literal.decl().name()
            
            # Try integer theory rules first
            if op_name in self.approximation_rules.get('int', {}):
                return self.approximation_rules['int'][op_name](literal)
            
            # Try real theory rules
            elif op_name in self.approximation_rules.get('real', {}):
                return self.approximation_rules['real'][op_name](literal)
            
            # Try boolean theory rules
            elif op_name in self.approximation_rules.get('bool', {}):
                return self.approximation_rules['bool'][op_name](literal)
        
        # Default: no approximation
        return literal, literal
    
    def generate_mutant_set(self, num_mutants=10) -> List[str]:
        """
        Generate a set of mutants using SAE strategy.
        
        Args:
            num_mutants: Number of mutants to generate
            
        Returns:
            List of SMT-LIB2 strings representing mutants
        """
        mutants = []
        
        for i in range(num_mutants):
            # Randomly choose approximation type
            approx_type = random.choice(['over', 'under'])
            
            # Generate approximation
            mutant = self.generate_skeletal_approximation(approx_type)
            
            if mutant and mutant not in mutants:
                mutants.append(mutant)
        
        return mutants
    
    def generate_literal_level_mutants(self) -> List[str]:
        """
        Generate mutants by applying literal-level mutations.
        
        Returns:
            List of SMT-LIB2 strings representing literal-level mutants
        """
        mutants = []
        
        for i, literal in enumerate(self.literals):
            # Create a copy of literals
            mutated_literals = self.literals.copy()
            
            # Apply approximation to the i-th literal
            over_approx, under_approx = self._get_approximation(literal)
            
            # Generate over-approximation mutant
            mutated_literals[i] = over_approx
            over_formula = And(mutated_literals) if len(mutated_literals) > 1 else mutated_literals[0]
            solver = Solver()
            solver.add(over_formula)
            mutants.append(solver.to_smt2())
            
            # Generate under-approximation mutant
            mutated_literals[i] = under_approx
            under_formula = And(mutated_literals) if len(mutated_literals) > 1 else mutated_literals[0]
            solver = Solver()
            solver.add(under_formula)
            mutants.append(solver.to_smt2())
        
        return mutants
    
    def verify_metamorphic_relation(self, original_result, mutant_result, approximation_type) -> bool:
        """
        Verify the metamorphic relation between original and mutant results.
        
        Args:
            original_result: Result from original formula (sat/unsat/unknown)
            mutant_result: Result from mutant formula
            approximation_type: Type of approximation used ('over' or 'under')
            
        Returns:
            True if metamorphic relation holds, False otherwise
        """
        if approximation_type == 'over':
            # Over-approximation: if original is SAT, mutant should be SAT
            # If mutant is UNSAT, original should be UNSAT
            if original_result == 'sat':
                return mutant_result == 'sat'
            elif mutant_result == 'unsat':
                return original_result == 'unsat'
        
        elif approximation_type == 'under':
            # Under-approximation: if original is UNSAT, mutant should be UNSAT
            # If mutant is SAT, original should be SAT
            if original_result == 'unsat':
                return mutant_result == 'unsat'
            elif mutant_result == 'sat':
                return original_result == 'sat'
        
        # For unknown results, we can't verify the relation
        return True


def main():
    """Main function for command-line usage."""
    parser = argparse.ArgumentParser(description='Skeletal Approximation Enumeration for SMT formulas')
    parser.add_argument('input_file', help='Input SMT-LIB2 file')
    parser.add_argument('output_file', help='Output file for mutants')
    parser.add_argument('--mode', choices=['over', 'under', 'both', 'literal'], 
                       default='both', help='Approximation mode')
    parser.add_argument('--num-mutants', type=int, default=10, 
                       help='Number of mutants to generate')
    
    args = parser.parse_args()
    
    # Initialize SAE mutator
    sae = SAEMutator()
    
    if not sae.init_from_file(args.input_file):
        print(f"Failed to initialize from {args.input_file}")
        return
    
    # Generate mutants based on mode
    mutants = []
    
    if args.mode == 'over':
        mutant = sae.generate_skeletal_approximation('over')
        if mutant:
            mutants.append(mutant)
    
    elif args.mode == 'under':
        mutant = sae.generate_skeletal_approximation('under')
        if mutant:
            mutants.append(mutant)
    
    elif args.mode == 'both':
        mutants = sae.generate_mutant_set(args.num_mutants)
    
    elif args.mode == 'literal':
        mutants = sae.generate_literal_level_mutants()
    
    # Write mutants to output file
    with open(args.output_file, 'w') as f:
        for i, mutant in enumerate(mutants):
            f.write(f"; Mutant {i+1}\n")
            f.write(mutant)
            f.write("\n\n")
    
    print(f"Generated {len(mutants)} mutants and saved to {args.output_file}")


if __name__ == "__main__":
    main() 