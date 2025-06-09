# coding: utf-8
"""Inter-Theory Mutator for SMT Solver Testing"""

import random
import re
from typing import Dict, Set, Optional, Tuple

# Handle both relative and absolute imports
from smtfuzz.inter.theory_bridge import Theory, TheoryBridge, ConversionType


class InterTheoryMutator:
    def __init__(self, seed: Optional[int] = None):
        if seed is not None:
            random.seed(seed)
        self.theory_bridge = TheoryBridge()
        self.variable_counter = 0
        self.mutation_history = []

    def mutate_formula(self, formula: str, mutation_intensity: int = 2) -> str:
        current_theories = self.theory_bridge.get_theories_in_formula(formula)
        mutated_formula = formula
        mutations_applied = []

        for i in range(mutation_intensity):
            mutation_type = self._choose_mutation_type(current_theories)

            if mutation_type == "add_conversion":
                mutated_formula, mutation_info = self._add_conversion_mutation(mutated_formula, current_theories)
            elif mutation_type == "add_length_constraint":
                mutated_formula, mutation_info = self._add_length_constraint(mutated_formula, current_theories)
            else:
                mutation_info = {"type": "no_mutation", "details": "No suitable mutation found"}

            mutations_applied.append(mutation_info)
            current_theories = self.theory_bridge.get_theories_in_formula(mutated_formula)

        self.mutation_history.append({
            "original_theories": list(self.theory_bridge.get_theories_in_formula(formula)),
            "final_theories": list(current_theories),
            "mutations": mutations_applied
        })

        return mutated_formula

    def _choose_mutation_type(self, current_theories: Set[Theory]) -> str:
        mutation_types = ["add_conversion"]
        if Theory.STRING in current_theories or Theory.SET in current_theories or Theory.BAG in current_theories:
            mutation_types.append("add_length_constraint")
        return random.choice(mutation_types)

    def _add_conversion_mutation(self, formula: str, current_theories: Set[Theory]) -> Tuple[str, Dict]:
        available_conversions = []
        for theory in current_theories:
            available_conversions.extend(self.theory_bridge.get_conversions_from_theory(theory))

        if not available_conversions:
            return formula, {"type": "conversion", "status": "failed"}

        conversion = random.choice(available_conversions)

        # Simple conversion mutations
        if conversion == "str_len":
            var = self._get_fresh_var("len")
            formula = self._add_variable_declaration(formula, var, "Int")
            mutation_code = f"(= {var} (str.len s))"
        elif conversion == "int_to_real":
            var = self._get_fresh_var("r")
            formula = self._add_variable_declaration(formula, var, "Real")
            mutation_code = f"(= {var} (to_real x))"
        else:
            mutation_code = f"; Conversion {conversion}"

        mutated_formula = self._insert_assertion(formula, mutation_code)
        return mutated_formula, {"type": "conversion", "conversion": conversion, "status": "success"}

    def _add_length_constraint(self, formula: str, current_theories: Set[Theory]) -> Tuple[str, Dict]:
        if Theory.STRING in current_theories:
            constraint = "(and (>= (str.len s) 1) (<= (str.len s) 100))"
        elif Theory.SET in current_theories:
            constraint = "(and (>= (card s) 0) (<= (card s) 50))"
        else:
            return formula, {"type": "length_constraint", "status": "failed"}

        mutated_formula = self._insert_assertion(formula, constraint)
        return mutated_formula, {"type": "length_constraint", "status": "success"}

    # Helper methods

    def _get_fresh_var(self, prefix: str = "v") -> str:
        self.variable_counter += 1
        return f"{prefix}{self.variable_counter}"

    def _insert_assertion(self, formula: str, assertion: str) -> str:
        lines = formula.split('\n')
        insert_pos = len(lines) - 2  # Before (check-sat) and (exit)
        lines.insert(insert_pos, f"(assert {assertion})")
        return '\n'.join(lines)

    def _add_variable_declaration(self, formula: str, var_name: str, var_type: str) -> str:
        decl = f"(declare-fun {var_name} () {var_type})"
        lines = formula.split('\n')
        lines.insert(1, decl)  # After set-logic
        return '\n'.join(lines)

    def get_mutation_history(self):
        return self.mutation_history

    def reset_history(self):
        self.mutation_history = []
