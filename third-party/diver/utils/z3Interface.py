from z3 import *


def ast_to_z3(ast, vars, logic, subs=[]):
    ty = ast.__class__.__name__

    ast = [i for i in ast if i not in ['(', ')', '_']]

    if ty == "Variable":
        variable = ast[0]
        return vars[variable]
    elif ty == "Bool":
        return BoolVal(ast[0] == "true")
    elif ty == "Constant":
        if logic & 1 != 0 and logic & 2 != 0:
            if "." in ast[0]:
                return RealVal(ast[0])
            else:
                return IntVal(ast[0])
        elif logic & 1 != 0:
            return RealVal(ast[0])
        else:
            return IntVal(ast[0])
    elif ty == "Const_String":
        return StringVal(ast[0][1:-1])

    op = ast[0]
    terms = ast[1:]

    if len(subs) != 0:
        z3s = subs
    else:
        z3s = []
        for t in terms:
            c = ast_to_z3(t, vars, logic)
            if c is None:
                return None
            z3s.append(c)

    if op == "and":
        tmp = And(z3s[0], z3s[1])
        for idx in range(2, len(z3s)):
            tmp = And(tmp, z3s[idx])
        return tmp
    elif op == "or":
        tmp = Or(z3s[0], z3s[1])
        for idx in range(2, len(z3s)):
            tmp = Or(tmp, z3s[idx])
        return tmp
    elif op == "xor":
        tmp = Xor(z3s[0], z3s[1])
        for idx in range(2, len(z3s)):
            tmp = Xor(tmp, z3s[idx])
        return tmp
    elif op == "not":
        return Not(z3s[0])
    elif op == "=>":
        return Implies(z3s[0], z3s[1])
    elif op == "ite":
        return If(z3s[0], z3s[1], z3s[2])
    elif op == "=":
        tmp = (z3s[0] == z3s[1])
        return tmp
    elif op == "distinct":
        tmp = Distinct(z3s[0], z3s[1])
        return tmp
    elif op == ">":
        return z3s[0] > z3s[1]
    elif op == ">=":
        return z3s[0] >= z3s[1]
    elif op == "<":
        return z3s[0] < z3s[1]
    elif op == "<=":
        return z3s[0] <= z3s[1]
    elif op == "+":
        tmp = (z3s[0] + z3s[1])
        for idx in range(2, len(z3s)):
            tmp = tmp + z3s[idx]
        return tmp
    elif op == "-":
        if len(z3s) == 1:
            return -z3s[0]
        tmp = (z3s[0] - z3s[1])
        for idx in range(2, len(z3s)):
            tmp = tmp - z3s[idx]
        return tmp
    elif op == "/":
        tmp = (z3s[0] / z3s[1])
        for idx in range(2, len(z3s)):
            tmp = tmp / z3s[idx]
        return tmp
    elif op == "*":
        tmp = (z3s[0] * z3s[1])
        for idx in range(2, len(z3s)):
            tmp = tmp * z3s[idx]
        return tmp
    elif op == "abs":
        return Abs(z3s[0])
    elif op == "mod":
        return (z3s[0] % z3s[1])
    elif op == "div":
        tmp = (z3s[0] / z3s[1])
        for idx in range(2, len(z3s)):
            tmp = tmp / z3s[idx]
        return tmp
    ### String Operator 
    elif op == "str.in_re":
        return InRe(z3s[0], z3s[1])
    elif op == "str.<=":
        return z3s[0] <= z3s[1]
    elif op == "str.<":
        return z3s[0] < z3s[1]
    elif op == "str.prefixof":
        return PrefixOf(z3s[0], z3s[1])
    elif op == "str.suffixof":
        return SuffixOf(z3s[0], z3s[1])
    elif op == "str.contains":
        return Contains(z3s[0], z3s[1])
    elif op == "str.is_digit":
        return CharIsDigit(z3s[0])
    elif op == "str.++":
        tmp = z3s[0] + z3s[1]
        for idx in range(2, len(z3s)):
            tmp = tmp + z3s[idx]
        return tmp
    elif op == "str.at":
        return z3s[0].at(z3s[1])
    elif op == "str.substr":
        return SubString(z3s[0], z3s[1], z3s[2])
    elif op == "str.replace":
        return Replace(z3s[0], z3s[1], z3s[2])
    elif op == "str.from_code":
        return StrFromCode(z3s[0])
    elif op == "str.from_int":
        return IntToStr(z3s[0])
    elif op == "str.len":
        return Length(z3s[0])
    elif op == "str.to_code":
        return StrToCode(z3s[0])
    elif op == "str.to_int":
        return StrToInt(z3s[0])
    elif op == "str.to_re":
        return Re(z3s[0])
    elif op == "str.indexof":
        return IndexOf(z3s[0], z3s[1], z3s[2])
    ### Regex Operator 
    elif op == "re.none":
        return Empty(ReSort(StringSort()))
    elif op == "re.allchar":
        return AllChar(ReSort(StringSort()))
    elif op == "re.all":
        return Full(ReSort(StringSort()))
    elif op == "re.++":
        tmp = (z3s[0] + z3s[1])
        for idx in range(2, len(z3s)):
            tmp = tmp + z3s[idx]
        return tmp
    elif op == "re.union":
        tmp = Union(z3s[0], z3s[1])
        for idx in range(2, len(z3s)):
            tmp = Union(tmp, z3s[idx])
        return tmp
    elif op == "re.inter":
        tmp = Intersect(z3s[0], z3s[1])
        for idx in range(2, len(z3s)):
            tmp = Intersect(tmp, z3s[idx])
        return tmp
    elif op == "re.*":
        return Star(z3s[0])
    elif op == "re.+":
        return Plus(z3s[0])
    elif op == "re.opt":
        return Option(z3s[0])
    elif op == "re.range":
        return Range(z3s[0], z3s[1])
    elif op == "re.comp":
        return Complement(z3s[0])
    elif op == "re.diff":
        return Diff(z3s[0], z3s[1])
    elif op == "re.loop":
        return Loop(z3s[0], z3s[1], z3s[2])
    else:
        return None
