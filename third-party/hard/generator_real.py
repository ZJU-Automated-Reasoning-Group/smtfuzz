from enum import Enum
import numpy as np
import random
import z3_other
import z3_time


class opt(Enum):
    #
    realneg = 1
    #
    realsub = 2
    realadd = 3
    realmul = 8
    realdiv = 9  ##
    #
    realle = 6  # <=
    reall = 7  # <
    realge = 4  # >=
    realg = 5  # >
    ##
    sin = 10
    cos = 11
    tan = 12
    ##
    abs = 13


class real:
    def __init__(self):
        self.isBool = False  #
        self.name = ""  #
        self.length = 0


oneVarOp = [1, 10, 11, 12, 13]
boolOutOp = [6, 7, 4, 5]


class gconstrains:
    def __init__(self):
        self.op = []  # 操作码
        self.index = 0
        self.outlist = []
        self.inlist = []

    class consop:
        def __init__(self):
            self.name = ""
            self.name_num = 0
            self.input = []
            self.output = real()

    def random_op(self):
        r = random.random()
        if r <= 0.9:
            rand = np.random.randint(1, 6)
        elif r >= 0.85:
            rand = np.random.randint(8, 10)
        else:
            rand = np.random.randint(10, 13)
        return rand

    def getopt(self, key):
        if key == 1 or key == 2:
            return "-"
        elif key == 3:
            return "+"
        elif key == 8:
            return "*"
        elif key == 9:
            return "/"
        elif key == 6:
            return "<="
        elif key == 7:
            return "<"
        elif key == 4:
            return ">="
        elif key == 5:
            return ">"
        else:
            return opt(key).name

    def greal(self, isBool=False):
        real_ins = real()
        real_ins.name = "real_" + str(self.index)
        self.index = self.index + 1
        real_ins.isBool = isBool
        self.inlist.append(real_ins)
        return real_ins

    def gOut(self, node):
        node.output.name = "real_" + str(self.index)
        self.index = self.index + 1
        if node.name_num in boolOutOp:
            node.output.isBool = True

    def addinput(self, reals_copy):
        input = None
        while len(reals_copy) > 0:
            if len(reals_copy) > 5:
                rand = np.random.randint(len(reals_copy) - 5, len(reals_copy))
            else:
                rand = np.random.randint(0, len(reals_copy))
            real = reals_copy[rand]
            reals_copy.remove(real)
            if real.isBool == False:
                input = real
                break
        if input == None:
            input = self.greal()
        return input

    def addinput1(self, reals_copy):
        input = None
        while len(reals_copy) > 0:
            real = reals_copy[-1]
            reals_copy.remove(real)
            if real.isBool == False:
                input = real
                break
        if input == None:
            input = self.greal()
        return input

    def addnode(self, rand, isRandom, reals_copy):
        # node信息
        node = self.consop()
        node.name = self.getopt(rand)
        node.name_num = rand
        ##input
        if isRandom:
            input1 = self.addinput(reals_copy)
        else:
            input1 = self.addinput1(reals_copy)
        node.input.append(input1)
        if node.name_num not in oneVarOp:
            if isRandom:
                input2 = self.addinput(reals_copy)
            else:
                input2 = self.addinput1(reals_copy)
            node.input.append(input2)
        self.gOut(node)
        self.outlist.append(node.output)
        self.op.append(node)
        return node.output

    def gcons(self, number):
        for _ in range(number):
            rand = self.random_op()
            reals = self.inlist + self.outlist
            reals_copy = reals[:]
            self.addnode(rand, True, reals_copy)

    # 转化为z3文件
    def tosmt(self, filename):
        f = open(filename, "w")
        f.write("(set-logic QF_NRA)\n")
        f.write("(set-option :produce-models true)\n")
        for i in range(len(self.inlist)):
            input = self.inlist[i]
            f.write("(declare-const %s Real)\n" % (input.name))
            f.write("(assert (not (= %s 0)))\n" % (input.name))
        for i in range(len(self.op)):
            output = self.op[i].output
            if self.op[i].name_num in boolOutOp:
                f.write("(declare-const %s Bool)\n" % (output.name))
            else:
                f.write("(declare-const %s Real)\n" % (output.name))
                f.write("(assert (not (= %s 0)))\n" % (output.name))
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
            real1 = cons_copy[rand1]
            rand2 = np.random.randint(0, length)
            real2 = cons_copy[rand2]
            if real1 != real2 and real1.isBool == real2.isBool:
                z = self.znode()
                z.name = "z_" + str(self.zindex)
                self.zindex += 1
                z.input1 = real1
                z.input2 = real2
                self.zlist.append(z)
                # self.allout.append(z)
                cons_copy.remove(real1)
                cons_copy.remove(real2)
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
