from enum import Enum
import numpy as np
import random
import z3_other
import z3_time


class opt(Enum):
    # Arithmetic operations
    intneg = 1      # -
    intadd = 2      # +
    intsub = 3      # -
    intmul = 4      # *
    intdiv = 5      # div
    intmod = 6      # mod
    intabs = 7      # abs
    # Comparison operations
    intle = 8       # <=
    intlt = 9       # <
    intge = 10      # >=
    intgt = 11      # >
    inteq = 12      # =
    intneq = 13     # distinct
    # Divisibility
    divisible = 14  # divisible


class integer:
    def __init__(self):
        self.isBool = False
        self.name = ""
        self.length = 0


oneVarOp = [1, 7]  # neg, abs
boolOutOp = [8, 9, 10, 11, 12, 13, 14]  # comparisons and divisibility
divisibleOp = [14]  # special handling for divisible


class gconstrains:
    def __init__(self):
        self.op = []
        self.index = 0
        self.outlist = []
        self.inlist = []

    class consop:
        def __init__(self):
            self.name = ""
            self.name_num = 0
            self.input = []
            self.output = integer()
            self.divisor = 0  # for divisible operation

    def random_op(self):
        r = random.random()
        if r <= 0.2:
            rand = np.random.randint(8, 15)  # comparison ops
        elif r > 0.8:
            rand = np.random.randint(5, 8)   # div, mod, abs
        else:
            rand = np.random.randint(1, 5)   # basic arithmetic
        return rand

    def getopt(self, key):
        operations = {
            1: "-", 2: "+", 3: "-", 4: "*", 5: "div", 6: "mod", 7: "abs",
            8: "<=", 9: "<", 10: ">=", 11: ">", 12: "=", 13: "distinct", 14: "divisible"
        }
        return operations.get(key, "unknown")

    def gint(self, isBool=False):
        int_o = integer()
        int_o.name = "int_" + str(self.index)
        self.index = self.index + 1
        int_o.isBool = isBool
        self.inlist.append(int_o)
        return int_o

    def gOut(self, node):
        node.output.name = "int_" + str(self.index)
        self.index = self.index + 1
        if node.name_num in boolOutOp:
            node.output.isBool = True
        else:
            node.output.isBool = False

    def addinput(self, ints_copy):
        r = random.random()
        input = None
        if r <= 1:
            while len(ints_copy) > 0:
                rand = np.random.randint(0, len(ints_copy))
                var = ints_copy[rand]
                ints_copy.remove(var)
                if var.isBool == False:
                    input = var
                    break
        if input == None:
            input = self.gint()
        return input

    def addinput1(self, ints_copy):
        input = None
        while len(ints_copy) > 0:
            var = ints_copy[-1]
            ints_copy.remove(var)
            if var.isBool == False:
                input = var
                break
        if input == None:
            input = self.gint()
        return input

    def addnode(self, rand, isRandom, ints_copy):
        node = self.consop()
        node.name = self.getopt(rand)
        node.name_num = rand
        
        # Handle input
        if isRandom:
            input1 = self.addinput(ints_copy)
        else:
            input1 = self.addinput1(ints_copy)
        node.input.append(input1)
        
        # Handle divisible operation specially
        if node.name_num in divisibleOp:
            node.divisor = random.randint(2, 10)  # random divisor
        elif node.name_num not in oneVarOp:
            if isRandom:
                input2 = self.addinput(ints_copy)
            else:
                input2 = self.addinput1(ints_copy)
            node.input.append(input2)
        
        self.gOut(node)
        self.outlist.append(node.output)
        self.op.append(node)
        return node.output

    def gcons(self, number):
        for _ in range(number):
            rand = self.random_op()
            ints = self.inlist + self.outlist
            ints_copy = ints[:]
            self.addnode(rand, True, ints_copy)

    def tosmt(self, filename):
        f = open(filename, "w")
        f.write("(set-logic QF_LIA)\n")
        f.write("(set-option :produce-models true)\n")
        
        # Declare input variables
        for i in range(len(self.inlist)):
            input_var = self.inlist[i]
            f.write("(declare-const %s Int)\n" % (input_var.name))
        
        # Declare output variables
        for i in range(len(self.op)):
            output = self.op[i].output
            if self.op[i].name_num in boolOutOp:
                f.write("(declare-const %s Bool)\n" % (output.name))
            else:
                f.write("(declare-const %s Int)\n" % (output.name))
        
        # Generate assertions
        for i in range(len(self.op)):
            inputlist = self.op[i].input
            length = len(inputlist)
            output = self.op[i].output
            
            if self.op[i].name_num in divisibleOp:
                # Special handling for divisible
                f.write("(assert (= %s (divisible %s %d)))\n" % 
                       (output.name, inputlist[0].name, self.op[i].divisor))
            else:
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
            int1 = cons_copy[rand1]
            rand2 = np.random.randint(0, length)
            int2 = cons_copy[rand2]
            if int1 != int2 and int1.isBool == int2.isBool:
                z = self.znode()
                z.name = "z_" + str(self.zindex)
                self.zindex += 1
                z.input1 = int1
                z.input2 = int2
                self.zlist.append(z)
                cons_copy.remove(int1)
                cons_copy.remove(int2)
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