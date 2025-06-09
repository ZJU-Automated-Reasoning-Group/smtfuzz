#!/usr/bin/env python3
"""Inter-Theory Mutation Engine Example"""

import sys
import os

from smtfuzz.inter.seed_generator import SeedGenerator
from smtfuzz.inter.inter_theory_mutator import InterTheoryMutator
from smtfuzz.inter.theory_bridge import Theory


def demo_seed_generation():
    print("=== Seed Generation Demo ===")
    generator = SeedGenerator()
    
    # Single theory seed
    print("\nString Theory Seed:")
    seed = generator.generate_single_theory_seed(Theory.STRING)
    print(seed)
    
    # Inter-theory seed
    print("\nString + Integer Seed:")
    seed = generator.generate_inter_theory_seed({Theory.STRING, Theory.INTEGER})
    print(seed)


def demo_mutation():
    print("\n=== Mutation Demo ===")
    
    # Start with a simple formula
    original = """(set-logic QF_SLIA)
(declare-fun s () String)
(assert (str.contains s "test"))
(check-sat)
(exit)"""
    
    print("\nOriginal Formula:")
    print(original)
    
    # Apply mutations
    mutator = InterTheoryMutator()
    mutated = mutator.mutate_formula(original, mutation_intensity=2)
    
    print("\nMutated Formula:")
    print(mutated)


def demo_batch_processing():
    print("\n=== Batch Processing Demo ===")
    
    generator = SeedGenerator()
    mutator = InterTheoryMutator()
    
    # Generate base seed
    base_seed = generator.generate_inter_theory_seed({Theory.STRING, Theory.INTEGER})
    
    print("Generating 3 mutations of base seed...")
    for i in range(3):
        mutated = mutator.mutate_formula(base_seed, mutation_intensity=1)
        print(f"\nMutation {i+1}:")
        print(mutated[:200] + "..." if len(mutated) > 200 else mutated)


if __name__ == "__main__":
    demo_seed_generation()
    demo_mutation()
    demo_batch_processing()
    print("\n=== Demo Complete ===") 