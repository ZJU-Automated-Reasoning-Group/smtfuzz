from enum import Enum
import numpy as np
import random
import z3_other
import z3_time


class opt(Enum):
    # String operations
    str_concat = 1      # str.++
    str_len = 2         # str.len
    str_substr = 3      # str.substr
    str_at = 4          # str.at
    str_indexof = 5     # str.indexof
    str_replace = 6     # str.replace
    str_prefixof = 7    # str.prefixof
    str_suffixof = 8    # str.suffixof
    str_contains = 9    # str.contains
    str_to_int = 10     # str.to_int
    int_to_str = 11     # int.to.str
    # String comparisons
    str_eq = 12         # =
    str_neq = 13        # distinct
    # Regular expressions
    str_in_re = 14      # str.in_re
    re_union = 15       # re.union
    re_inter = 16       # re.inter
    re_star = 17        # re.*
    re_plus = 18        # re.+
    re_opt = 19         # re.opt


class string:
    def __init__(self):
        self.isBool = False
        self.isInt = False
        self.isRegex = False
        self.name = ""
        self.length = 0


oneVarOp = [2, 4, 10, 11, 17, 18, 19]  # len, at, to_int, int_to_str, re.*, re.+, re.opt
boolOutOp = [7, 8, 9, 12, 13, 14]  # prefixof, suffixof, contains, eq, neq, in_re
intOutOp = [2, 5, 10]  # len, indexof, to_int
regexOutOp = [15, 16, 17, 18, 19]  # regex operations
threeVarOp = [3, 6]  # substr, replace
twoVarOp = [1, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16]  # most binary operations


class gconstrains:
    def __init__(self):
        self.op = []
        self.index = 0
        self.outlist = []
        self.inlist = []
        self.string_literals = ["\"hello\"", "\"world\"", "\"test\"", "\"abc\"", "\"xyz\"", "\"\""]

    class consop:
        def __init__(self):
            self.name = ""
            self.name_num = 0
            self.input = []
            self.output = string()
            self.start_pos = 0  # for substr
            self.length_param = 0  # for substr

    def random_op(self):
        r = random.random()
        if r <= 0.3:
            rand = np.random.randint(1, 7)   # basic string ops
        elif r <= 0.6:
            rand = np.random.randint(7, 12)  # comparison and conversion ops
        else:
            rand = np.random.randint(12, 20) # advanced ops and regex
        return rand

    def getopt(self, key):
        operations = {
            1: "str.++", 2: "str.len", 3: "str.substr", 4: "str.at", 5: "str.indexof",
            6: "str.replace", 7: "str.prefixof", 8: "str.suffixof", 9: "str.contains",
            10: "str.to_int", 11: "int.to.str", 12: "=", 13: "distinct", 14: "str.in_re",
            15: "re.union", 16: "re.inter", 17: "re.*", 18: "re.+", 19: "re.opt"
        }
        return operations.get(key, "unknown")

    def gstring(self, isBool=False, isInt=False, isRegex=False):
        str_o = string()
        if isInt:
            str_o.name = "int_" + str(self.index)
            str_o.isInt = True
        elif isRegex:
            str_o.name = "re_" + str(self.index)
            str_o.isRegex = True
        else:
            str_o.name = "str_" + str(self.index)
        self.index = self.index + 1
        str_o.isBool = isBool
        self.inlist.append(str_o)
        return str_o

    def gOut(self, node):
        if node.name_num in intOutOp:
            node.output.name = "int_" + str(self.index)
            node.output.isInt = True
        elif node.name_num in regexOutOp:
            node.output.name = "re_" + str(self.index)
            node.output.isRegex = True
        else:
            node.output.name = "str_" + str(self.index)
        
        self.index = self.index + 1
        
        if node.name_num in boolOutOp:
            node.output.isBool = True
        else:
            node.output.isBool = False

    def addinput(self, strs_copy, need_int=False, need_regex=False):
        r = random.random()
        input_var = None
        
        if r <= 0.8:  # Try to use existing variables
            while len(strs_copy) > 0:
                rand = np.random.randint(0, len(strs_copy))
                var = strs_copy[rand]
                strs_copy.remove(var)
                
                if need_int and var.isInt and not var.isBool:
                    input_var = var
                    break
                elif need_regex and var.isRegex:
                    input_var = var
                    break
                elif not need_int and not need_regex and not var.isBool and not var.isInt and not var.isRegex:
                    input_var = var
                    break
        
        # Create new variable if needed
        if input_var == None:
            if need_int:
                input_var = self.gstring(isInt=True)
            elif need_regex:
                input_var = self.gstring(isRegex=True)
            else:
                input_var = self.gstring()
        
        return input_var

    def addinput1(self, strs_copy, need_int=False, need_regex=False):
        input_var = None
        while len(strs_copy) > 0:
            var = strs_copy[-1]
            strs_copy.remove(var)
            
            if need_int and var.isInt and not var.isBool:
                input_var = var
                break
            elif need_regex and var.isRegex:
                input_var = var
                break
            elif not need_int and not need_regex and not var.isBool and not var.isInt and not var.isRegex:
                input_var = var
                break
        
        if input_var == None:
            if need_int:
                input_var = self.gstring(isInt=True)
            elif need_regex:
                input_var = self.gstring(isRegex=True)
            else:
                input_var = self.gstring()
        
        return input_var

    def addnode(self, rand, isRandom, strs_copy):
        node = self.consop()
        node.name = self.getopt(rand)
        node.name_num = rand
        
        # Handle different operation types
        if rand == 3:  # substr needs string, int, int
            if isRandom:
                input1 = self.addinput(strs_copy)  # string
                input2 = self.addinput(strs_copy, need_int=True)  # start position
                input3 = self.addinput(strs_copy, need_int=True)  # length
            else:
                input1 = self.addinput1(strs_copy)
                input2 = self.addinput1(strs_copy, need_int=True)
                input3 = self.addinput1(strs_copy, need_int=True)
            node.input.extend([input1, input2, input3])
        elif rand == 6:  # replace needs string, string, string
            if isRandom:
                input1 = self.addinput(strs_copy)  # source string
                input2 = self.addinput(strs_copy)  # pattern
                input3 = self.addinput(strs_copy)  # replacement
            else:
                input1 = self.addinput1(strs_copy)
                input2 = self.addinput1(strs_copy)
                input3 = self.addinput1(strs_copy)
            node.input.extend([input1, input2, input3])
        elif rand == 11:  # int.to.str needs int
            if isRandom:
                input1 = self.addinput(strs_copy, need_int=True)
            else:
                input1 = self.addinput1(strs_copy, need_int=True)
            node.input.append(input1)
        elif rand == 14:  # str.in_re needs string and regex
            if isRandom:
                input1 = self.addinput(strs_copy)  # string
                input2 = self.addinput(strs_copy, need_regex=True)  # regex
            else:
                input1 = self.addinput1(strs_copy)
                input2 = self.addinput1(strs_copy, need_regex=True)
            node.input.extend([input1, input2])
        elif rand in regexOutOp and rand in oneVarOp:  # unary regex ops
            if isRandom:
                input1 = self.addinput(strs_copy, need_regex=True)
            else:
                input1 = self.addinput1(strs_copy, need_regex=True)
            node.input.append(input1)
        elif rand in regexOutOp:  # binary regex ops
            if isRandom:
                input1 = self.addinput(strs_copy, need_regex=True)
                input2 = self.addinput(strs_copy, need_regex=True)
            else:
                input1 = self.addinput1(strs_copy, need_regex=True)
                input2 = self.addinput1(strs_copy, need_regex=True)
            node.input.extend([input1, input2])
        elif rand in oneVarOp:  # unary operations
            if isRandom:
                input1 = self.addinput(strs_copy)
            else:
                input1 = self.addinput1(strs_copy)
            node.input.append(input1)
        else:  # binary operations
            if isRandom:
                input1 = self.addinput(strs_copy)
                input2 = self.addinput(strs_copy)
            else:
                input1 = self.addinput1(strs_copy)
                input2 = self.addinput1(strs_copy)
            node.input.extend([input1, input2])
        
        self.gOut(node)
        self.outlist.append(node.output)
        self.op.append(node)
        return node.output

    def gcons(self, number):
        for _ in range(number):
            rand = self.random_op()
            strs = self.inlist + self.outlist
            strs_copy = strs[:]
            self.addnode(rand, True, strs_copy)

    def tosmt(self, filename):
        f = open(filename, "w")
        f.write("(set-logic QF_SLIA)\n")
        f.write("(set-option :produce-models true)\n")
        
        # Declare input variables
        for i in range(len(self.inlist)):
            input_var = self.inlist[i]
            if input_var.isInt:
                f.write("(declare-const %s Int)\n" % (input_var.name))
            elif input_var.isRegex:
                f.write("(declare-const %s RegLan)\n" % (input_var.name))
            else:
                f.write("(declare-const %s String)\n" % (input_var.name))
        
        # Declare output variables
        for i in range(len(self.op)):
            output = self.op[i].output
            if self.op[i].name_num in boolOutOp:
                f.write("(declare-const %s Bool)\n" % (output.name))
            elif output.isInt:
                f.write("(declare-const %s Int)\n" % (output.name))
            elif output.isRegex:
                f.write("(declare-const %s RegLan)\n" % (output.name))
            else:
                f.write("(declare-const %s String)\n" % (output.name))
        
        # Generate assertions
        for i in range(len(self.op)):
            inputlist = self.op[i].input
            length = len(inputlist)
            output = self.op[i].output
            
            f.write("(assert (= %s (%s " % (output.name, self.op[i].name))
            for j in range(length):
                if j == length - 1:
                    f.write("%s)))\n" % inputlist[j].name)
                else:
                    f.write("%s " % inputlist[j].name)
        f.close()


class modelopt(Enum):  # not and or
    bnot = 1
    band = 2
    bor = 3


for i in range(1, 4):
    op = modelopt(i)
    op.label = op.name[1:]


class gmodel:
    def __init__(self):
        self.modelop = []
        self.zlist = []
        self.zindex = 0
        self.cons = gconstrains()

    class znode:
        def __init__(self):
            self.name = ""
            self.input1 = None
            self.input2 = None

    class gmop:
        def __init__(self):
            self.name = ""
            self.input = []  # znode
            self.output = ""

    def randopt(self):
        r = random.random()
        if r < 0.1:
            rand = 1
        elif r > 0.7:
            rand = 2
        else:
            rand = 3
        return rand

    def gznode(self, cons_copy):
        length = len(cons_copy)
        trytime = 0
        while length > 1 and trytime < 100:
            trytime += 1
            rand1 = np.random.randint(0, length)
            str1 = cons_copy[rand1]
            rand2 = np.random.randint(0, length)
            str2 = cons_copy[rand2]
            if str1 != str2 and str1.isBool == str2.isBool:
                z = self.znode()
                z.name = "z_" + str(self.zindex)
                self.zindex += 1
                z.input1 = str1
                z.input2 = str2
                self.zlist.append(z)
                cons_copy.remove(str1)
                cons_copy.remove(str2)
                break

    def addopt(self, allOut):
        mnode = self.gmop()
        if len(allOut) == 0:
            print("no znode")
        elif len(allOut) == 1:
            mnode.name = "not"
            input1 = allOut[0]
            mnode.input.append(input1)
            if input1.name == "not" or input1.name == "and" or input1.name == "or":
                mnode.output = "( not " + input1.output + " )"
            else:
                mnode.output = "( not " + input1.name + " )"
            allOut.remove(input1)
        else:
            rand = self.randopt()
            o = modelopt(rand)
            mnode.name = o.label
            rand1 = np.random.randint(0, len(allOut))
            input1 = allOut[rand1]
            mnode.input.append(input1)
            allOut.remove(input1)
            if mnode.name == "not":
                if input1.name == "not" or input1.name == "and" or input1.name == "or":
                    mnode.output = "( not " + input1.output + " )"
                else:
                    mnode.output = "( not " + input1.name + " )"
            else:
                rand2 = np.random.randint(0, len(allOut))
                input2 = allOut[rand2]
                mnode.input.append(input2)
                allOut.remove(input2)
                if input1.name == "not" or input1.name == "and" or input1.name == "or":
                    input1 = input1.output
                else:
                    input1 = input1.name
                if input2.name == "not" or input2.name == "and" or input2.name == "or":
                    input2 = input2.output
                else:
                    input2 = input2.name
                mnode.output = "( " + mnode.name + " " + input1 + " " + input2 + " )"
        self.modelop.append(mnode)
        return mnode

    def modeltree(self, cons_num, model_num):
        self.cons.gcons(cons_num)
        cons = self.cons.outlist[:]
        for i in range(model_num):
            self.gznode(cons)
        allOut = self.zlist[:] + self.modelop[:]
        while len(allOut) > 1:
            mnode = self.addopt(allOut)
            allOut.append(mnode)

    def tosmt(self, filename):
        self.cons.tosmt(filename)
        f = open(filename, "a")
        length = len(self.zlist)
        for i in range(length):
            f.write("(declare-const %s Bool)\n" % self.zlist[i].name)
        for i in range(length):
            f.write("(assert (= %s (= %s %s)))\n" % (
                self.zlist[i].name, self.zlist[i].input1.name, self.zlist[i].input2.name))
        f.write("(assert ")
        f.write(self.modelop[-1].output)
        f.write(" )\n")
        f.write("(check-sat)\n")
        f.write("(get-model)\n")
        f.write("(exit)\n")
        f.close() 