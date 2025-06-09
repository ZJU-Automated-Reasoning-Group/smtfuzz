# coding: utf-8
"""Seed Generator for Inter-Theory Mutations"""

import random
from typing import Set

# Handle both relative and absolute imports
from smtfuzz.inter.theory_bridge import Theory


class SeedGenerator:
    def __init__(self):
        self.variable_counter = 0
        
    def _get_fresh_var(self, prefix: str = "v") -> str:
        self.variable_counter += 1
        return f"{prefix}{self.variable_counter}"
    
    def generate_single_theory_seed(self, theory: Theory, complexity: int = 3) -> str:
        generators = {
            Theory.STRING: self._generate_string_seed,
            Theory.INTEGER: self._generate_integer_seed,
            Theory.REAL: self._generate_real_seed,
            Theory.BITVECTOR: self._generate_bitvector_seed,
            Theory.FLOATINGPOINT: self._generate_fp_seed,
            Theory.ARRAY: self._generate_array_seed,
            Theory.SET: self._generate_set_seed,
            Theory.BAG: self._generate_bag_seed,
        }
        return generators.get(theory, self._generate_integer_seed)(complexity)
    
    def generate_inter_theory_seed(self, theories: Set[Theory], complexity: int = 5) -> str:
        if len(theories) < 2:
            base_theory = list(theories)[0] if theories else Theory.INTEGER
            theories.add(Theory.STRING if base_theory != Theory.STRING else Theory.REAL)
        
        # Simple inter-theory seed with string-integer connection
        return f"""(set-logic ALL)
(declare-fun s () String)
(declare-fun x () Int)
(assert (= x (str.len s)))
(assert (> x 0))
(check-sat)
(exit)"""
    
    def _generate_string_seed(self, complexity: int) -> str:
        return f"""(set-logic QF_SLIA)
(declare-fun s () String)
(assert (str.contains s "test"))
(assert (= (str.len s) 5))
(check-sat)
(exit)"""
    
    def _generate_integer_seed(self, complexity: int) -> str:
        return f"""(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (< x 100))
(check-sat)
(exit)"""
    
    def _generate_real_seed(self, complexity: int) -> str:
        return f"""(set-logic QF_LRA)
(declare-fun r () Real)
(assert (> r 0.0))
(assert (< r 10.5))
(check-sat)
(exit)"""
    
    def _generate_bitvector_seed(self, complexity: int) -> str:
        return f"""(set-logic QF_BV)
(declare-fun bv () (_ BitVec 8))
(assert (bvugt bv #b00000000))
(assert (bvult bv #b11111111))
(check-sat)
(exit)"""
    
    def _generate_fp_seed(self, complexity: int) -> str:
        return f"""(set-logic QF_FP)
(declare-fun fp () (_ FloatingPoint 8 24))
(assert (fp.gt fp ((_ to_fp 8 24) RNE 0.0)))
(check-sat)
(exit)"""
    
    def _generate_array_seed(self, complexity: int) -> str:
        return f"""(set-logic QF_AX)
(declare-fun arr () (Array Int Int))
(declare-fun i () Int)
(assert (> (select arr i) 0))
(check-sat)
(exit)"""
    
    def _generate_set_seed(self, complexity: int) -> str:
        return f"""(set-logic ALL)
(declare-fun s () (Set Int))
(declare-fun x () Int)
(assert (member x s))
(check-sat)
(exit)"""
    
    def _generate_bag_seed(self, complexity: int) -> str:
        return f"""(set-logic ALL)
(declare-fun b () (Bag Int))
(declare-fun x () Int)
(assert (> (bag.count x b) 0))
(check-sat)
(exit)"""
    
    def generate_random_seed(self, max_theories: int = 3, complexity: int = 4) -> str:
        all_theories = list(Theory)
        num_theories = random.randint(1, min(max_theories, len(all_theories)))
        chosen_theories = set(random.sample(all_theories, num_theories))
        
        if num_theories == 1:
            return self.generate_single_theory_seed(list(chosen_theories)[0], complexity)
        else:
            return self.generate_inter_theory_seed(chosen_theories, complexity)


if __name__ == "__main__":
    print("Testing Seed Generator...")
    
    generator = SeedGenerator()
    
    # Test single theory seed
    print("\nString theory seed:")
    seed = generator.generate_single_theory_seed(Theory.STRING)
    print(seed)
    
    # Test inter-theory seed
    print("\nInter-theory seed:")
    seed = generator.generate_inter_theory_seed({Theory.STRING, Theory.INTEGER})
    print(seed)
    
    print("\nTest completed successfully!") 