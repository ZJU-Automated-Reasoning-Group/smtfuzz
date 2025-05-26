
from __future__ import annotations

from typing import NamedTuple, Union, Any


#operators for arithmetic
class Add(NamedTuple):
    x: Any
    y: Any
    
class Sub(NamedTuple):
    x: Any
    y: Any

class Mul(NamedTuple):
    x: Any
    y: Any

class IntDiv(NamedTuple):
    x: Any
    y: Any

class Mod(NamedTuple):
    x: Any
    y: Any

class Div(NamedTuple):
    x: Any
    y: Any

class Leq(NamedTuple):
    x: Any
    y: Any

class Geq(NamedTuple):
    x: Any
    y: Any

class Lt(NamedTuple):
    x: Any
    y: Any

class Gt(NamedTuple):
    x: Any
    y: Any

class Neg(NamedTuple):
    x: Any

class Abs(NamedTuple):
    x: Any


# (to_real Int Real)
# (to_int Real Int)
# (is_int Real Bool)
class ToReal(NamedTuple):
    x: Any

class ToInt(NamedTuple):
    x: Any

class IsInt(NamedTuple):
    x: Any


ARITH_OPS = [Add, Sub, Mul, Div, Mod, IntDiv, Leq, Geq, Lt, Gt, Neg, Abs, ToReal, ToInt, IsInt]

# # Allow constant folding via an eval function
# def eval_math(car, cdr):
#     # This could be a literal encoded in a string
#     try:
#         return float(car)
#     except:
#         pass

#     # Else it is an operation with arguments
#     op = car
#     args = cdr
#     try:
#         a = float(args[0])
#         b = float(args[1])
#         if op == Add:
#             return a + b
#         if op == Sub:
#             return a - b
#         if op == Mul:
#             return a * b
#         if op == Div and b != 0.0:
#             return a / b
#     except:
#         pass
#     return None



def eval_arith(car, cdr):
    try:
        return float(car)
    except:
        pass
    op = car
    args = cdr
    try:
        for i in range(len(args)):
            args[i] = float(args[i])
        a = float(args[0])
        b = float(args[1])
        if op == Add:
            if len(args) == 1:
                return a
            elif len(args) == 2:
                return a + b
            else:
                for i in range(1, len(args)):
                    a += args[i]
                return a
        if op == Mul:
            if len(args) == 1:
                return a
            elif len(args) == 2:
                return a * b
            else:
                for i in range(1, len(args)):
                    a *= args[i]
                return a
        if op == Sub:
            if len(args) == 1:
                return a
            elif len(args) == 2:
                return a - b
            else:
                for i in range(1, len(args)):
                    a -= args[i]
                return a
            # return a - b
        if op == Div and b != 0.0:
            return int(a) / int(b)
        if op == Mod and b != 0.0:
            return int(a) % int(b)
        if op == RealDiv and b != 0.0:
            return a / b
        if op == LEQ:
            return a <= b
        if op == GEQ:
            return a >= b
        if op == LT:
            return a < b
        if op == GT:
            return a > b
        if op == Neg:
            return -a
        if op == Abs:
            return abs(a)
    except:
        pass
    return None

# operators for bool
class Not(NamedTuple):
    x: Any

class Implies(NamedTuple):
    x: Any
    y: Any

class And(NamedTuple):
    x: Any
    y: Any

class Or(NamedTuple):
    x: Any
    y: Any

class Xor(NamedTuple):
    x: Any
    y: Any


class Eq(NamedTuple):
    x: Any
    y: Any

class Distinct(NamedTuple):
    x: Any
    y: Any

class Ite(NamedTuple):
    x: Any
    y: Any
    z: Any

class TRUE(NamedTuple):
    def __str__(self):
        return "true"
    def __repr__(self):
        return "true"

class FALSE(NamedTuple):
    def __str__(self):
        return "false"
    def __repr__(self):
        return "false"
    
class EmptyString(NamedTuple):
    def __str__(self):
        return '""'
    def __repr__(self):
        return '""'


BOOL_OPS = [Not, Implies, And, Or, Xor, Eq, Distinct, Ite, TRUE, FALSE]


# ; ### funs from strings
# ;
# ; ## Core functions 
# (str.++ String String String :left-assoc)
# (str.len String Int)
# (str.< String String Bool :chainable)

class Concat(NamedTuple):
    x: Any
    y: Any

class StrLen(NamedTuple):
    x: Any

class StrLt(NamedTuple):
    x: Any
    y: Any

# ;
# ; ## Regular expression functions
# (str.to_re String RegLan) 
# (str.in_re String RegLan Bool) 
# (re.none RegLan)
# (re.all RegLan)
# (re.allchar RegLan)
# (re.++ RegLan RegLan RegLan :left-assoc)
# (re.union RegLan RegLan RegLan :left-assoc)
# (re.inter RegLan RegLan RegLan :left-assoc)
# (re.* RegLan RegLan) 

class StrToRe(NamedTuple):
    x: Any

class StrInRe(NamedTuple):
    x: Any
    y: Any

class ReConcat(NamedTuple):
    x: Any
    y: Any

class ReUnion(NamedTuple):
    x: Any
    y: Any

class ReIntersect(NamedTuple):
    x: Any
    y: Any

class ReStar(NamedTuple):
    x: Any

# ;
# ; ## Regular expression functions
# (str.<= String String Bool :chainable)   
# (str.at String Int String)
# (str.substr String Int Int String)
# (str.prefixof String String Bool)
# (str.suffixof String String Bool)
# (str.contains String String Bool)
# (str.indexof String String Int Int)
# (str.replace String String String String)
# (str.replace_all String String String String)
# (str.replace_re String RegLan String String) 
# (str.replace_re_all String RegLan String String) 
# (re.comp RegLan RegLan)
# (re.diff RegLan RegLan RegLan :left-assoc)
# (re.+ RegLan RegLan)
# (re.opt RegLan RegLan)
# (re.range String String RegLan)

class StrLeq(NamedTuple):
    x: Any
    y: Any

class StrAt(NamedTuple):
    x: Any
    y: Any

class StrSubstr(NamedTuple):
    x: Any
    y: Any
    z: Any

class StrPrefixof(NamedTuple):
    x: Any
    y: Any

class StrSuffixof(NamedTuple):
    x: Any
    y: Any

class StrContains(NamedTuple):
    x: Any
    y: Any

class StrIndexof(NamedTuple):
    x: Any
    y: Any
    z: Any

class StrReplace(NamedTuple):
    x: Any
    y: Any
    z: Any

class StrReplaceAll(NamedTuple):
    x: Any
    y: Any
    z: Any

class StrReplaceRe(NamedTuple):
    x: Any
    y: Any
    z: Any

class StrReplaceReAll(NamedTuple):
    x: Any
    y: Any
    z: Any

class ReComp(NamedTuple):
    x: Any


class ReDiff(NamedTuple):
    x: Any
    y: Any

class RePlus(NamedTuple):
    x: Any

class ReOpt(NamedTuple):
    x: Any

class ReRange(NamedTuple):
    x: Any
    y: Any


# ; 
# ; ## Maps to and from integers
# (str.is_digit String Bool)
# (str.to_code String Int) 
# (str.from_code Int String) 
# (str.to_int String Int)
# (str.from_int Int String)

class StrIsDigit(NamedTuple):
    x: Any

class StrToCode(NamedTuple):
    x: Any

class StrFromCode(NamedTuple):
    x: Any

class StrToInt(NamedTuple):
    x: Any

class IntToStr(NamedTuple):
    x: Any

class StrFromInt(NamedTuple):
    x: Any

class ReNone(NamedTuple):
    pass

class ReAll(NamedTuple):
    pass

class ReAllChar(NamedTuple):
    pass

class BvConcat(NamedTuple):
    x: Any
    y: Any

class Extract(NamedTuple):
    x: Any
    y: Any
    z: Any

class BvSub(NamedTuple):
    x: Any
    y: Any

class BvAdd(NamedTuple):
    x: Any
    y: Any

class BvConst(NamedTuple):
    x: Any

class BvOr(NamedTuple):
    x: Any
    y: Any

class BvAnd(NamedTuple):
    x: Any
    y: Any

class BvXor(NamedTuple):
    x: Any
    y: Any

class BvNot(NamedTuple):
    x: Any

class BvUlt(NamedTuple):
    x: Any
    y: Any

class BvSlt(NamedTuple):
    x: Any
    y: Any

class BvMul(NamedTuple):
    x: Any
    y: Any

class BvNeg(NamedTuple):
    x: Any

class ZeroExtend(NamedTuple):
    x: Any
    y: Any

class SignExtend(NamedTuple):
    x: Any
    y: Any

class BvSgt(NamedTuple):
    x: Any
    y: Any

class Other(NamedTuple):
    symbol: Any
    arg1: Any
    arg2: Any




# STR_OPS = [StrLen, StrLt, StrToRe, StrInRe, ReUnion, ReInter, ReStar, StrLeq, StrAt, StrSubstr, StrPrefixof, StrSuffixof, StrContains, StrIndexof, StrReplace, StrReplaceAll, StrReplaceRe, StrReplaceReAll, ReComp, ReDiff, RePlus, ReOpt, ReRange, StrIsDigit, StrToCode, StrFromCode, StrToInt, StrFromInt]

