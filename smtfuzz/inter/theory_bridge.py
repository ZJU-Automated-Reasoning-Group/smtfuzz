# coding: utf-8
"""Theory Bridge for Inter-Theory Mutations"""

import random
from enum import Enum
from typing import Dict, List, Set, Optional


class Theory(Enum):
    STRING = "String"
    INTEGER = "Int"
    REAL = "Real"
    BITVECTOR = "BitVec"
    FLOATINGPOINT = "FloatingPoint"
    ARRAY = "Array"
    SET = "Set"
    BAG = "Bag"
    UNINTERPRETED = "UninterpretedFunction"


class ConversionType(Enum):
    LENGTH = "length"
    CONVERSION = "conversion"
    ENCODING = "encoding"
    ABSTRACTION = "abstraction"


class TheoryBridge:
    def __init__(self):
        self.conversion_map = {
            "str_len": {"from": Theory.STRING, "to": Theory.INTEGER, "function": "str.len",
                        "type": ConversionType.LENGTH},
            "str_to_int": {"from": Theory.STRING, "to": Theory.INTEGER, "function": "str.to_int",
                           "type": ConversionType.CONVERSION},
            "str_from_int": {"from": Theory.INTEGER, "to": Theory.STRING, "function": "str.from_int",
                             "type": ConversionType.CONVERSION},
            "set_card": {"from": Theory.SET, "to": Theory.INTEGER, "function": "card", "type": ConversionType.LENGTH},
            "bag_card": {"from": Theory.BAG, "to": Theory.INTEGER, "function": "bag.card",
                         "type": ConversionType.LENGTH},
            "int_to_real": {"from": Theory.INTEGER, "to": Theory.REAL, "function": "to_real",
                            "type": ConversionType.CONVERSION},
            "real_to_int": {"from": Theory.REAL, "to": Theory.INTEGER, "function": "to_int",
                            "type": ConversionType.CONVERSION},
            "bv_to_nat": {"from": Theory.BITVECTOR, "to": Theory.INTEGER, "function": "bv2nat",
                          "type": ConversionType.CONVERSION},
            "int_to_bv": {"from": Theory.INTEGER, "to": Theory.BITVECTOR, "function": "int2bv",
                          "type": ConversionType.CONVERSION},
            "fp_to_sbv": {"from": Theory.FLOATINGPOINT, "to": Theory.BITVECTOR, "function": "fp.to_sbv",
                          "type": ConversionType.CONVERSION},
            "fp_to_ubv": {"from": Theory.FLOATINGPOINT, "to": Theory.BITVECTOR, "function": "fp.to_ubv",
                          "type": ConversionType.CONVERSION},
            "real_to_fp": {"from": Theory.REAL, "to": Theory.FLOATINGPOINT, "function": "to_fp",
                           "type": ConversionType.CONVERSION},
            "fp_to_real": {"from": Theory.FLOATINGPOINT, "to": Theory.REAL, "function": "fp.to_real",
                           "type": ConversionType.CONVERSION},
        }
        self.theory_compatibility = self._build_compatibility_matrix()

    def _build_compatibility_matrix(self):
        matrix = {}
        for conv_name, conv_info in self.conversion_map.items():
            key = (conv_info["from"], conv_info["to"])
            matrix.setdefault(key, []).append(conv_name)
        return matrix

    def get_conversions_from_theory(self, theory: Theory) -> List[str]:
        return [name for name, info in self.conversion_map.items() if info["from"] == theory]

    def get_conversions_to_theory(self, theory: Theory) -> List[str]:
        return [name for name, info in self.conversion_map.items() if info["to"] == theory]

    def get_random_conversion(self, from_theory: Optional[Theory] = None, to_theory: Optional[Theory] = None) -> \
    Optional[str]:
        candidates = [name for name, info in self.conversion_map.items()
                      if (not from_theory or info["from"] == from_theory) and
                      (not to_theory or info["to"] == to_theory)]
        return random.choice(candidates) if candidates else None

    def get_conversion_info(self, conversion_name: str) -> Optional[Dict]:
        return self.conversion_map.get(conversion_name)

    def get_theories_in_formula(self, formula_str: str) -> Set[Theory]:
        theories = set()
        theory_keywords = {
            Theory.STRING: ["str.", "String"],
            Theory.INTEGER: ["+", "-", "*", "div", "mod", "Int"],
            Theory.REAL: ["/", "Real"],
            Theory.BITVECTOR: ["bv", "#b", "#x", "BitVec"],
            Theory.FLOATINGPOINT: ["fp.", "FloatingPoint"],
            Theory.ARRAY: ["select", "store", "Array"],
            Theory.SET: ["insert", "member", "Set"],
            Theory.BAG: ["bag.", "Bag"]
        }

        for theory, keywords in theory_keywords.items():
            if any(keyword in formula_str for keyword in keywords):
                theories.add(theory)
        return theories


if __name__ == "__main__":
    print("Testing Theory Bridge...")

    bridge = TheoryBridge()

    # Test conversion mappings
    print(f"\nAvailable conversions: {len(bridge.conversion_map)}")
    for name, info in list(bridge.conversion_map.items())[:3]:
        print(f"  {name}: {info['from'].value} -> {info['to'].value}")

    # Test theory detection
    test_formula = "(assert (= x (str.len s)))"
    theories = bridge.get_theories_in_formula(test_formula)
    print(f"\nDetected theories in '{test_formula}': {[t.value for t in theories]}")
