"""
MIT License

Copyright (c) 2023 The histfuzz authors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""


return_type = {"xor": "Bool", "=": "Bool", "distinct": "Bool", "div": "Int", "mod": "Int", "abs": "Int",
               "<": "Bool", ">": "Bool", "<=": "Bool", ">=": "Bool", "to_real": "Real", "to_int": "Int",
               "is_int": "Bool", "str.++": "String", "str.len": "Int", "str.<": "Bool", "str.in_re": "Bool",
               "str.<=": "Int", "str.at": "String", "str.substr": "String", "str.prefixof": "Bool",
               "str.suffixof": "Bool", "str.contains": "Bool", "str.indexof": "Int",
               "str.replace": "String", "str.replace_all": "String", "str.replace_re": "String",
               "str.replace_re_all": "String", "str.is_digit": "Bool", "str.to_code": "Int",
               "str.from_code": "String", "str.to_int": "Int", "str.from_int": "String", "+": "Unknown",
               "-": "Unknown", "*": "Unknown", "/": "Unknown", "ite": "Unknown", "concat": "BitVec",
               "bvneg": "BitVec", "bvand": "BitVec", "bvnot": "BitVec", "bvor": "BitVec", "bvxor": "BitVec",
               "bvadd": "BitVec", "bvsub": "BitVec", "bvmul": "BitVec", "bvudiv": "BitVec", "bvurem": "BitVec",
               "bvshl": "BitVec", "bvlshr": "BitVec", "bvashr": "BitVec", "bvult": "Bool", "bvule": "Bool",
               "bvslt": "Bool", "bvsgt": "Bool", "bvsdiv": "BitVec", "fp.abs": "FloatingPoint",
               "fp.neg": "FloatingPoint", "fp.add": "FloatingPoint", "fp.sub": "FloatingPoint",
               "fp.mul": "FloatingPoint", "fp.div": "FloatingPoint", "fp.sqrt": "FloatingPoint",
               "fp.rem": "FloatingPoint", "fp.roundToIntegral": "FloatingPoint", "fp.fma": "FloatingPoint",
               "fp.min": "FloatingPoint", "fp.max": "FloatingPoint", "fp.max_i": "FloatingPoint",
               "fp.leq": "Bool", "fp.lt": "Bool",
               "fp.geq": "Bool", "fp.gt": "Bool", "fp.eq": "Bool", "fp.isNormal": "Bool",
               "fp.isSubnormal": "Bool", "fp.isZero": "Bool", "fp.isInfinite": "Bool", "fp.isNaN": "Bool",
               "fp.isNegative": "Bool", "fp.isPositive": "Bool", "and": "Bool", "or": "Bool", "not": "Bool",
               "=>": "Bool", "fp": "FloatingPoint", "fp.to_real": "Real", "_ +oo": "FloatingPoint",
               "bv2nat": "Int", "store": "Array"}
