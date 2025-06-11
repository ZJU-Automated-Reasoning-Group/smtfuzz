# coding: utf-8
"""Test suite for Skeletal Approximation Enumeration (SAE) strategy"""

import unittest
import tempfile
import os

try:
    from z3 import *
    z3_available = True
except ImportError:
    print("Warning: Z3 not available, skipping Z3-dependent tests")
    z3_available = False

import sys
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

if z3_available:
    from sae.sae_mutator import SAEMutator
    from sae.sae_utils import get_formula_complexity, apply_predicate_symbol_transformation


class TestSAEBasic(unittest.TestCase):
    """Basic SAE functionality tests."""
    
    def setUp(self):
        if not z3_available:
            self.skipTest("Z3 not available")
            
        self.mutator = SAEMutator()
        self.test_content = """
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun p () Bool)
(assert (and (> x 5) (or p (< y 10))))
(check-sat)
"""
        self.temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False)
        self.temp_file.write(self.test_content)
        self.temp_file.close()
    
    def tearDown(self):
        if hasattr(self, 'temp_file') and os.path.exists(self.temp_file.name):
            os.unlink(self.temp_file.name)
    
    def test_initialization_and_literals(self):
        """Test mutator initialization and literal extraction."""
        result = self.mutator.init_from_file(self.temp_file.name)
        self.assertTrue(result)
        self.assertTrue(self.mutator.success)
        self.assertIsNotNone(self.mutator.formula)
        self.assertGreater(len(self.mutator.literals), 0)
    
    def test_approximation_generation(self):
        """Test approximation generation."""
        self.mutator.init_from_file(self.temp_file.name)
        
        over_approx = self.mutator.generate_skeletal_approximation('over')
        under_approx = self.mutator.generate_skeletal_approximation('under')
        
        self.assertIsInstance(over_approx, str)
        self.assertIsInstance(under_approx, str)
        self.assertGreater(len(over_approx), 0)
        self.assertGreater(len(under_approx), 0)
    
    def test_mutant_generation(self):
        """Test mutant generation."""
        self.mutator.init_from_file(self.temp_file.name)
        mutants = self.mutator.generate_mutant_set(num_mutants=3)
        
        self.assertIsInstance(mutants, list)
        self.assertGreater(len(mutants), 0)
        
        for mutant in mutants:
            self.assertIsInstance(mutant, str)
            self.assertIn('(assert', mutant)
    
    def test_metamorphic_relations(self):
        """Test metamorphic relation verification."""
        self.assertTrue(self.mutator.verify_metamorphic_relation('sat', 'sat', 'over'))
        self.assertFalse(self.mutator.verify_metamorphic_relation('sat', 'unsat', 'over'))
        self.assertTrue(self.mutator.verify_metamorphic_relation('unsat', 'unsat', 'under'))
        self.assertFalse(self.mutator.verify_metamorphic_relation('unsat', 'sat', 'under'))


class TestSAEUtils(unittest.TestCase):
    """Test SAE utility functions."""
    
    def setUp(self):
        if not z3_available:
            self.skipTest("Z3 not available")
            
        self.x = Int('x')
        self.y = Int('y')
        self.p = Bool('p')
        self.formula = And(self.x > 5, Or(self.p, self.y < 10))
    
    def test_formula_complexity(self):
        """Test formula complexity analysis."""
        complexity = get_formula_complexity(self.formula)
        
        self.assertIsInstance(complexity, dict)
        self.assertIn('num_atoms', complexity)
        self.assertIn('num_variables', complexity)
        self.assertGreater(complexity['num_atoms'], 0)
        self.assertGreater(complexity['num_variables'], 0)
    
    def test_predicate_transformation(self):
        """Test predicate symbol transformations."""
        literal = self.x > 5
        negated = apply_predicate_symbol_transformation(literal, 'negate')
        self.assertIsNotNone(negated)


class TestSAEErrorHandling(unittest.TestCase):
    """Test error handling."""
    
    def test_invalid_file_handling(self):
        """Test handling of invalid files."""
        if not z3_available:
            self.skipTest("Z3 not available")
            
        mutator = SAEMutator()
        result = mutator.init_from_file("nonexistent_file.smt2")
        self.assertFalse(result)
        self.assertFalse(mutator.success)


if __name__ == '__main__':
    unittest.main(verbosity=1)
