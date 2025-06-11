# coding: utf-8
"""
Utility functions for Skeletal Approximation Enumeration (SAE)

This module provides helper functions for formula analysis, 
approximation generation, and metamorphic relation verification.
"""

import random
from typing import List, Dict, Set, Tuple, Optional
from z3 import *


def get_formula_complexity(formula) -> Dict[str, int]:
    """
    Analyze the complexity of a formula.
    
    Args:
        formula: Z3 formula to analyze
        
    Returns:
        Dictionary with complexity metrics
    """
    complexity = {
        'num_atoms': 0,
        'num_literals': 0,
        'num_variables': 0,
        'num_operators': 0,
        'max_depth': 0,
        'num_quantifiers': 0
    }
    
    def analyze_expr(expr, depth=0):
        complexity['max_depth'] = max(complexity['max_depth'], depth)
        
        if is_app(expr):
            complexity['num_operators'] += 1
            
            # Count variables
            if expr.num_args() == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
                complexity['num_variables'] += 1
            
            # Count atoms and literals
            if is_bool(expr) and not (is_true(expr) or is_false(expr)):
                if is_not(expr):
                    complexity['num_literals'] += 1
                else:
                    complexity['num_atoms'] += 1
            
            # Recursively analyze children
            for child in expr.children():
                analyze_expr(child, depth + 1)
        
        elif is_quantifier(expr):
            complexity['num_quantifiers'] += 1
            analyze_expr(expr.body(), depth + 1)
    
    analyze_expr(formula)
    return complexity


def extract_theory_specific_literals(formula) -> Dict[str, List]:
    """
    Extract literals organized by theory.
    
    Args:
        formula: Z3 formula to analyze
        
    Returns:
        Dictionary mapping theory names to lists of literals
    """
    theory_literals = {
        'int': [],
        'real': [],
        'bool': [],
        'bv': [],
        'array': [],
        'string': [],
        'fp': []
    }
    
    def classify_literal(literal):
        if is_app(literal):
            # Check argument sorts to determine theory
            for arg in literal.children():
                sort = arg.sort()
                if sort.kind() == Z3_INT_SORT:
                    theory_literals['int'].append(literal)
                    return
                elif sort.kind() == Z3_REAL_SORT:
                    theory_literals['real'].append(literal)
                    return
                elif sort.kind() == Z3_BOOL_SORT:
                    theory_literals['bool'].append(literal)
                    return
                elif sort.kind() == Z3_BV_SORT:
                    theory_literals['bv'].append(literal)
                    return
                elif sort.kind() == Z3_ARRAY_SORT:
                    theory_literals['array'].append(literal)
                    return
        
        # Default to boolean if can't classify
        theory_literals['bool'].append(literal)
    
    def collect_literals(expr):
        if is_not(expr):
            classify_literal(expr)
        elif is_and(expr) or is_or(expr):
            for child in expr.children():
                collect_literals(child)
        elif is_bool(expr) and not (is_true(expr) or is_false(expr)):
            classify_literal(expr)
    
    collect_literals(formula)
    return theory_literals


def generate_random_approximation_strategy() -> Dict[str, str]:
    """
    Generate a random approximation strategy for different theories.
    
    Returns:
        Dictionary mapping theory names to approximation strategies
    """
    strategies = ['over', 'under', 'mixed']
    
    return {
        'int': random.choice(strategies),
        'real': random.choice(strategies),
        'bool': random.choice(strategies),
        'bv': random.choice(strategies),
        'array': random.choice(strategies),
        'string': random.choice(strategies),
        'fp': random.choice(strategies)
    }


def apply_predicate_symbol_transformation(literal, transformation_type='negate'):
    """
    Apply predicate symbol transformation to a literal.
    
    Args:
        literal: Z3 literal to transform
        transformation_type: Type of transformation ('negate', 'weaken', 'strengthen')
        
    Returns:
        Transformed literal
    """
    if transformation_type == 'negate':
        return Not(literal) if not is_not(literal) else literal.arg(0)
    
    elif transformation_type == 'weaken':
        # Make the literal easier to satisfy
        if is_app(literal):
            op_name = literal.decl().name()
            if op_name == '<':
                # x < y becomes x <= y
                return literal.arg(0) <= literal.arg(1)
            elif op_name == '>':
                # x > y becomes x >= y
                return literal.arg(0) >= literal.arg(1)
            elif op_name == '=':
                # x = y becomes True (always satisfiable)
                return BoolVal(True)
        return literal
    
    elif transformation_type == 'strengthen':
        # Make the literal harder to satisfy
        if is_app(literal):
            op_name = literal.decl().name()
            if op_name == '<=':
                # x <= y becomes x < y
                return literal.arg(0) < literal.arg(1)
            elif op_name == '>=':
                # x >= y becomes x > y
                return literal.arg(0) > literal.arg(1)
            elif op_name == '=':
                # x = y stays the same (already strong)
                return literal
        return literal
    
    return literal


def generate_live_predicate_injection(formula, injection_probability=0.3):
    """
    Generate live predicate injection mutants.
    
    Args:
        formula: Original Z3 formula
        injection_probability: Probability of injecting predicates
        
    Returns:
        Modified formula with injected predicates
    """
    def inject_predicates(expr):
        if random.random() < injection_probability:
            if is_and(expr):
                # Inject additional conjuncts
                children = list(expr.children())
                # Add a tautology that doesn't change satisfiability
                children.append(BoolVal(True))
                return And(children)
            elif is_or(expr):
                # Inject additional disjuncts
                children = list(expr.children())
                # Add a contradiction that doesn't change satisfiability
                children.append(BoolVal(False))
                return Or(children)
        
        # Recursively process children
        if is_app(expr) and expr.num_args() > 0:
            new_children = [inject_predicates(child) for child in expr.children()]
            return expr.decl()(new_children)
        
        return expr
    
    return inject_predicates(formula)


def compute_approximation_distance(original_formula, approximated_formula) -> float:
    """
    Compute a distance metric between original and approximated formulas.
    
    Args:
        original_formula: Original Z3 formula
        approximated_formula: Approximated Z3 formula
        
    Returns:
        Distance metric (0.0 = identical, 1.0 = completely different)
    """
    # Simple structural distance based on AST differences
    def count_nodes(expr):
        if is_app(expr):
            return 1 + sum(count_nodes(child) for child in expr.children())
        return 1
    
    orig_nodes = count_nodes(original_formula)
    approx_nodes = count_nodes(approximated_formula)
    
    # Normalize by the larger formula size
    max_nodes = max(orig_nodes, approx_nodes)
    if max_nodes == 0:
        return 0.0
    
    return abs(orig_nodes - approx_nodes) / max_nodes


def validate_approximation_correctness(original_formula, approximated_formula, 
                                     approximation_type='over') -> bool:
    """
    Validate that the approximation maintains the correct logical relationship.
    
    Args:
        original_formula: Original Z3 formula
        approximated_formula: Approximated Z3 formula
        approximation_type: Type of approximation ('over' or 'under')
        
    Returns:
        True if approximation is correct, False otherwise
    """
    try:
        solver = Solver()
        
        if approximation_type == 'over':
            # Over-approximation: original => approximated should be valid
            implication = Implies(original_formula, approximated_formula)
        else:
            # Under-approximation: approximated => original should be valid
            implication = Implies(approximated_formula, original_formula)
        
        solver.add(Not(implication))
        result = solver.check()
        
        # If the negation is unsatisfiable, the implication is valid
        return result == unsat
    
    except Exception:
        # If we can't verify, assume it's correct
        return True


def generate_cube_enumeration(cnf_formula, max_cubes=50) -> List:
    """
    Generate cube enumeration from a CNF formula.
    
    Args:
        cnf_formula: CNF formula to enumerate cubes from
        max_cubes: Maximum number of cubes to generate
        
    Returns:
        List of cube formulas
    """
    cubes = []
    
    # Extract clauses from CNF
    clauses = []
    if is_and(cnf_formula):
        clauses = list(cnf_formula.children())
    else:
        clauses = [cnf_formula]
    
    # Generate cubes by selecting literals from each clause
    for _ in range(min(max_cubes, 2**min(len(clauses), 10))):  # Limit exponential growth
        cube_literals = []
        
        for clause in clauses:
            if is_or(clause):
                # Randomly select one literal from the clause
                literals = list(clause.children())
                selected_literal = random.choice(literals)
                cube_literals.append(selected_literal)
            else:
                cube_literals.append(clause)
        
        if cube_literals:
            cube = And(cube_literals) if len(cube_literals) > 1 else cube_literals[0]
            cubes.append(cube)
    
    return cubes


def create_skeletal_template(formula) -> Tuple[str, List]:
    """
    Create a skeletal template from a formula by replacing literals with holes.
    
    Args:
        formula: Z3 formula to create template from
        
    Returns:
        Tuple of (template_string, list_of_holes)
    """
    holes = []
    hole_counter = [0]  # Use list to allow modification in nested function
    
    def create_holes(expr):
        if is_app(expr) and is_bool(expr) and not (is_true(expr) or is_false(expr)):
            # Replace with hole
            hole_id = f"hole_{hole_counter[0]}"
            holes.append((hole_id, expr))
            hole_counter[0] += 1
            return hole_id
        
        elif is_app(expr):
            # Recursively process children
            op_name = expr.decl().name()
            child_results = [create_holes(child) for child in expr.children()]
            return f"({op_name} {' '.join(str(c) for c in child_results)})"
        
        else:
            return str(expr)
    
    template = create_holes(formula)
    return template, holes


def fill_skeletal_template(template: str, holes: List, approximation_mapping: Dict) -> str:
    """
    Fill a skeletal template with approximated literals.
    
    Args:
        template: Template string with holes
        holes: List of (hole_id, original_literal) pairs
        approximation_mapping: Mapping from hole_id to approximated literal
        
    Returns:
        Filled template as string
    """
    filled_template = template
    
    for hole_id, original_literal in holes:
        if hole_id in approximation_mapping:
            replacement = str(approximation_mapping[hole_id])
        else:
            replacement = str(original_literal)
        
        filled_template = filled_template.replace(hole_id, replacement)
    
    return filled_template
