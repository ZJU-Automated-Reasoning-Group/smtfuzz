# Inter-Theory Mutation Engine

A specialized component of SMTFuzz for generating and mutating SMT-LIB2 formulas with interactions between different SMT
theories.

## Components

- **`theory_bridge.py`** - Theory conversion mappings
- **`seed_generator.py`** - Seed formula generation
- **`inter_theory_mutator.py`** - Main mutation engine

## Supported Theories

String, Integer, Real, BitVector, FloatingPoint, Array, Set, Bag, UninterpretedFunction

## Key Conversions

- String ↔ Integer: `str.len`, `str.to_int`, `str.from_int`
- Integer ↔ Real: `to_real`, `to_int`
- BitVector ↔ Integer: `bv2nat`, `int2bv`
- FloatingPoint ↔ Real/BV: `fp.to_real`, `fp.to_sbv`
- Set/Bag ↔ Integer: `card`, `bag.card`

