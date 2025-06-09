from enum import Enum
import numpy as np
import random
import z3_other
import z3_time


# import generator_bv
# import generator_real
# import g_transform

class opt(Enum):
    roundNearestTiesToEven = 1
    roundNearestTiesToAway = 2
    roundTowardPositive = 3
    roundTowardNegative = 4
    roundTowardZero = 5

    abs = 6
    neg = 7
    add = 8
    sub = 9
    mul = 12
    fma = 11  ##(x+y)*z
    roundToIntegral = 10
    min = 13
    max = 14
    ###
    div = 15
    sqrt = 16
    rem = 17

    ##
    leq = 18
    lt = 19
    geq = 20
    gt = 21
    eq = 22

    ##
    isNormal = 23
    isSubnormal = 24
    isZero = 25
    isInfinite = 26
    isNaN = 27
    isNegative = 28
    isPositive = 29


class fp_var:
    def __init__(self):
        self.name = ""
        self.length = 0  # 长度
        self.isBool = False


oneVarOp = [6, 7, 10, 16, 23, 24, 25, 26, 27, 28, 29]
threeVarOp = [11]
boolOutOp = [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
needRoundOp = [8, 9, 10, 11, 12, 15, 16]


class gconstrains:
    def __init__(self):
        self.op = []
        self.index = 0
        self.outlist = []
        self.inlist = []
        # self.translist=[]
        # abs,neg,roundToIntergral,sqrt  23-29

    class consop:
        def __init__(self):  ##
            self.name = ""
            self.name_num = 0
            self.roundingmode = ""
            self.input = []
            self.output = fp_var()

    def random_roundmode(self):
        # r=random.random()
        # if r<0.95:
        rand = np.random.randint(1, 5)
        # else:
        # rand=5
        return rand

    def random_op(self):
        r = random.random()
        if r <= 0.95 and r > 0.9:
            rand = np.random.randint(23, 30)
        elif r > 0.95 and r <= 0.97:
            rand = np.random.randint(13, 15)
        elif r > 0.97 and r <= 0.98:
            rand = 6
        elif r > 0.98:
            rand = 10
        elif r <= 0.9 and r > 0.85:
            rand = np.random.randint(18, 23)
        elif r <= 0.85 and r > 0.78:
            rand = np.random.randint(11, 13)
        else:
            rand = np.random.randint(7, 10)
        return rand

    def gfp_var(self, length=128, isBool=False):
        var_ins = fp_var()
        var_ins.length = length
        var_ins.isBool = isBool
        var_ins.name = "fp_" + str(self.index)
        self.index += 1
        self.inlist.append(var_ins)
        return var_ins

    # def gtransVar(self,var1,var2):###调用转换接口  other->fp(fp->fp   16<->32)  不直接使用
    #     transexp=g_transform.tramsform()
    #     tnode=transexp.tNode()
    #     ##舍入模式
    #     rand_round=self.random_roundmode()
    #     roundingmode=opt(rand_round).name
    #     tnode=transexp.transfom(var1,var2,self.index,32,32,roundingmode)
    #     self.index+=1
    #     self.inlist.append(tnode.output)
    #     self.translist.append(tnode.outString)
    #     return tnode.output

    def gOut(self, node):
        node.output.name = "fp_" + str(self.index)
        self.index += 1
        if node.name_num in boolOutOp:
            node.output.isBool = True
            node.output.length = 1
        else:
            node.output.isBool = False
            node.output.length = node.input[0].length

    def addinput(self, vars_copy):
        input = None
        while len(vars_copy) > 0:
            rand = np.random.randint(0, len(vars_copy))
            var = vars_copy[rand]
            vars_copy.remove(var)
            if var.isBool == False:
                input = var
                break
        if input == None:
            input = self.gfp_var()
            # input=self.gtransVar("bv","fp")
        return input

    def addinput1(self, vars_copy):
        input = None
        while len(vars_copy) > 0:
            var = vars_copy[-1]
            vars_copy.remove(var)
            if var.isBool == False:
                input = var
                break
        if input == None:
            input = self.gfp_var()
            # input=self.gtransVar("bv","fp")
        return input

    def addnode(self, rand, isRandom, vars_copy):  ###
        ##node信息
        node = self.consop()
        # rand=self.random_op()
        node.name = opt(rand).name
        node.name_num = rand
        rand_round = self.random_roundmode()
        node.roundingmode = opt(rand_round).name
        ##input
        if isRandom:
            input1 = self.addinput(vars_copy)
        else:
            input1 = self.addinput1(vars_copy)
        node.input.append(input1)
        if node.name_num not in oneVarOp:
            if isRandom:
                input2 = self.addinput(vars_copy)
            else:
                input2 = self.addinput1(vars_copy)
            node.input.append(input2)
        if node.name_num in threeVarOp:
            if isRandom:
                input3 = self.addinput(vars_copy)
            else:
                input3 = self.addinput1(vars_copy)
            node.input.append(input3)
        self.gOut(node)
        self.outlist.append(node.output)
        self.op.append(node)
        return node.output

    def gcons(self, number):
        for _ in range(number):
            rand = self.random_op()
            vars = self.outlist + self.inlist
            vars_copy = vars[:]
            self.addnode(rand, True, vars_copy)

    def trans(self, length):
        if length == 16:
            eb = 5
            sb = 11
        elif length == 32:
            eb = 8
            sb = 24
        elif length == 64:
            eb = 11
            sb = 53
        elif length == 128:
            eb = 15
            sb = 113
        return eb, sb

    def tosmt(self, filename):
        f = open(filename, "w")
        f.write("(set-logic QF_FP)\n")
        f.write("(set-option :produce-models true)\n")
        for i in range(len(self.inlist)):
            input = self.inlist[i]

            eb, sb = self.trans(input.length)
            f.write("(declare-const %s (_ FloatingPoint %d %d))\n" % (input.name, eb, sb))
            f.write("(assert (not (= %s (_ +zero %d %d))))\n" % (input.name, eb, sb))
            f.write("(assert (not (= %s (_ -zero %d %d))))\n" % (input.name, eb, sb))
        for i in range(len(self.op)):
            output = self.op[i].output
            if self.op[i].name_num in boolOutOp:
                f.write("(declare-const %s Bool)\n" % (output.name))
            else:
                eb, sb = self.trans(output.length)
                f.write("(declare-const %s (_ FloatingPoint %d %d))\n" % (output.name, eb, sb))
                f.write("(assert (not (= %s (_ +zero %d %d))))\n" % (output.name, eb, sb))
                f.write("(assert (not (= %s (_ -zero %d %d))))\n" % (output.name, eb, sb))
        # for i in range(len(self.translist)):
        #     f.write(self.translist[i])
        for i in range(len(self.op)):
            inputlist = self.op[i].input
            length = len(inputlist)
            output = self.op[i].output
            if self.op[i].name_num not in needRoundOp:
                f.write("(assert (= %s (fp.%s " % (output.name, self.op[i].name))
            else:
                f.write("(assert (= %s (fp.%s %s " % (output.name, self.op[i].name, self.op[i].roundingmode))
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
        # self.allout=[]

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
        if r < 0.3:
            rand = 1
        elif r > 0.7:
            rand = 2
        else:
            rand = 3
        return rand

    def gznode(self, cons_copy):  #
        length = len(cons_copy)
        trytime = 0
        while length > 1 and trytime < 100:
            trytime += 1
            rand1 = np.random.randint(0, length)
            var1 = cons_copy[rand1]
            rand2 = np.random.randint(0, length)
            var2 = cons_copy[rand2]
            if var1 != var2 and var1.length == var2.length and var1.isBool == var2.isBool:
                z = self.znode()
                z.name = "z_" + str(self.zindex)
                self.zindex += 1
                z.input1 = var1
                z.input2 = var2
                self.zlist.append(z)
                # self.allout.append(z)
                cons_copy.remove(var1)  #
                cons_copy.remove(var2)
                length -= 2
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
