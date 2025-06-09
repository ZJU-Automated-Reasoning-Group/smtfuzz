import cvc5
from cvc5 import Kind


def ast_to_cvc5(ast, solver, vars, logic, subs=[]):
    try:
        ty = ast.__class__.__name__

        ast = [i for i in ast if i not in ['(', ')', '_']]

        if ty == "Variable":
            variable = ast[0]
            return vars[variable]
        elif ty == "Bool":
            return solver.mkBoolean(ast[0] == "true")
        elif ty == "Constant":
            if logic & 1 != 0 and logic & 2 != 0:
                if "." in ast[0]:
                    return solver.mkReal(float(ast[0]))
                else:
                    return solver.mkInteger(int(ast[0]))
            elif logic & 1 != 0:
                return solver.mkReal(float(ast[0]))
            else:
                return solver.mkInteger(int(ast[0]))
        elif ty == "Const_String":
            if r"\u" in ast[0][1:-1]:
                return solver.mkString(ast[0][1:-1], useEscSequences=True)
            else:
                return solver.mkString(ast[0][1:-1])

        op = ast[0]
        terms = ast[1:]

        if len(subs) != 0:
            cvcs = subs
        else:
            cvcs = []
            for t in terms:
                cvcs.append(ast_to_cvc5(t, solver, vars, logic))

        if op == "and":
            tmp = solver.mkTerm(Kind.AND, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.AND, tmp, cvcs[idx])
            return tmp
        elif op == "or":
            tmp = solver.mkTerm(Kind.OR, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.OR, tmp, cvcs[idx])
            return tmp
        elif op == "xor":
            tmp = solver.mkTerm(Kind.XOR, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.XOR, tmp, cvcs[idx])
            return tmp
        elif op == "not":
            return solver.mkTerm(Kind.NOT, cvcs[0])
        elif op == "=>":
            return solver.mkTerm(Kind.IMPLIES, cvcs[0], cvcs[1])
        elif op == "ite":
            return solver.mkTerm(Kind.ITE, cvcs[0], cvcs[1], cvcs[2])
        elif op == "=":
            tmp = solver.mkTerm(Kind.EQUAL, cvcs[0], cvcs[1])
            return tmp
        elif op == "distinct":
            tmp = solver.mkTerm(Kind.DISTINCT, cvcs[0], cvcs[1])
            return tmp
        elif op == ">":
            tmp = solver.mkTerm(Kind.GT, cvcs[0], cvcs[1])
            return tmp
        elif op == ">=":
            tmp = solver.mkTerm(Kind.GEQ, cvcs[0], cvcs[1])
            return tmp
        elif op == "<":
            tmp = solver.mkTerm(Kind.LT, cvcs[0], cvcs[1])
            return tmp
        elif op == "<=":
            tmp = solver.mkTerm(Kind.LEQ, cvcs[0], cvcs[1])
            return tmp
        elif op == "+":
            tmp = solver.mkTerm(Kind.ADD, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.ADD, tmp, cvcs[idx])
            return tmp
        elif op == "-":
            if len(cvcs) == 1:
                return solver.mkTerm(Kind.NEG, cvcs[0])
            tmp = solver.mkTerm(Kind.SUB, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.SUB, tmp, cvcs[idx])
            return tmp
        elif op == "/":
            tmp = solver.mkTerm(Kind.DIVISION, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.DIVISION, tmp, cvcs[idx])
            return tmp
        elif op == "*":
            tmp = solver.mkTerm(Kind.MULT, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.MULT, tmp, cvcs[idx])
            return tmp
        elif op == "abs":
            return solver.mkTerm(Kind.ABS, cvcs[0])
        elif op == "int.pow2":
            return solver.mkTerm(Kind.POW2, cvcs[0])
        elif op == "mod":
            return solver.mkTerm(Kind.INTS_MODULUS, cvcs[0], cvcs[1])
        elif op == "div":
            return solver.mkTerm(Kind.INTS_DIVISION, cvcs[0], cvcs[1])
        elif op == "iand":
            return solver.mkTerm(Kind.IAND, cvcs[0], cvcs[1])
        ### String Operator 
        elif op == "str.in_re":
            return solver.mkTerm(Kind.STRING_IN_REGEXP, cvcs[0], cvcs[1])
        elif op == "str.<=":
            return solver.mkTerm(Kind.STRING_LEQ, cvcs[0], cvcs[1])
        elif op == "str.<":
            return solver.mkTerm(Kind.STRING_LT, cvcs[0], cvcs[1])
        elif op == "str.prefixof":
            return solver.mkTerm(Kind.STRING_PREFIX, cvcs[0], cvcs[1])
        elif op == "str.suffixof":
            return solver.mkTerm(Kind.STRING_SUFFIX, cvcs[0], cvcs[1])
        elif op == "str.contains":
            return solver.mkTerm(Kind.STRING_CONTAINS, cvcs[0], cvcs[1])
        elif op == "str.is_digit":
            return solver.mkTerm(Kind.STRING_IS_DIGIT, cvcs[0])
        elif op == "str.++":
            tmp = solver.mkTerm(Kind.STRING_CONCAT, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.STRING_CONCAT, tmp, cvcs[idx])
            return tmp
        elif op == "str.at":
            return solver.mkTerm(Kind.STRING_CHARAT, cvcs[0], cvcs[1])
        elif op == "str.substr":
            return solver.mkTerm(Kind.STRING_SUBSTR, cvcs[0], cvcs[1], cvcs[2])
        elif op == "str.replace_all":
            return solver.mkTerm(Kind.STRING_REPLACE_ALL, cvcs[0], cvcs[1], cvcs[2])
        elif op == "str.replace_re_all":
            return solver.mkTerm(Kind.STRING_REPLACE_RE_ALL, cvcs[0], cvcs[1], cvcs[2])
        elif op == "str.replace_re":
            return solver.mkTerm(Kind.STRING_REPLACE_RE, cvcs[0], cvcs[1], cvcs[2])
        elif op == "str.replace":
            return solver.mkTerm(Kind.STRING_REPLACE, cvcs[0], cvcs[1], cvcs[2])
        elif op == "str.from_code":
            return solver.mkTerm(Kind.STRING_FROM_CODE, cvcs[0])
        elif op == "str.from_int":
            return solver.mkTerm(Kind.STRING_FROM_INT, cvcs[0])
        elif op == "str.len":
            return solver.mkTerm(Kind.STRING_LENGTH, cvcs[0])
        elif op == "str.to_code":
            return solver.mkTerm(Kind.STRING_TO_CODE, cvcs[0])
        elif op == "str.to_int":
            return solver.mkTerm(Kind.STRING_TO_INT, cvcs[0])
        elif op == "str.to_upper":
            return solver.mkTerm(Kind.STRING_TO_UPPER, cvcs[0])
        elif op == "str.to_lower":
            return solver.mkTerm(Kind.STRING_TO_LOWER, cvcs[0])
        elif op == "str.rev":
            return solver.mkTerm(Kind.STRING_REV, cvcs[0])
        elif op == "str.update":
            return solver.mkTerm(Kind.STRING_UPDATE, cvcs[0], cvcs[1], cvcs[2])
        elif op == "str.indexof_re":
            return solver.mkTerm(Kind.STRING_INDEXOF_RE, cvcs[0], cvcs[1], cvcs[2])
        elif op == "str.to_re":
            return solver.mkTerm(Kind.STRING_TO_REGEXP, cvcs[0])
        elif op == "str.indexof":
            return solver.mkTerm(Kind.STRING_INDEXOF, cvcs[0], cvcs[1], cvcs[2])
        ### Regex Operator 
        elif op == "re.none":
            return solver.mkRegexpNone()
        elif op == "re.allchar":
            return solver.mkRegexpAllchar()
        elif op == "re.all":
            return solver.mkRegexpAll()
        elif op == "re.++":
            tmp = solver.mkTerm(Kind.REGEXP_CONCAT, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.REGEXP_CONCAT, tmp, cvcs[idx])
            return tmp
        elif op == "re.union":
            tmp = solver.mkTerm(Kind.REGEXP_UNION, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.REGEXP_UNION, tmp, cvcs[idx])
            return tmp
        elif op == "re.inter":
            tmp = solver.mkTerm(Kind.REGEXP_INTER, cvcs[0], cvcs[1])
            for idx in range(2, len(cvcs)):
                tmp = solver.mkTerm(Kind.REGEXP_INTER, tmp, cvcs[idx])
            return tmp
        elif op == "re.*":
            return solver.mkTerm(Kind.REGEXP_STAR, cvcs[0])
        elif op == "re.+":
            return solver.mkTerm(Kind.REGEXP_PLUS, cvcs[0])
        elif op == "re.opt":
            return solver.mkTerm(Kind.REGEXP_OPT, cvcs[0])
        elif op == "re.range":
            return solver.mkTerm(Kind.REGEXP_RANGE, cvcs[0], cvcs[1])
        elif op == "re.comp":
            return solver.mkTerm(Kind.REGEXP_COMPLEMENT, cvcs[0])
        elif op == "re.diff":
            return solver.mkTerm(Kind.REGEXP_DIFF, cvcs[0], cvcs[1])
        else:
            return None
    except Exception as e:
        return None
