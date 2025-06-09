from enum import Enum
import numpy as np
import random

import z3_time


class opt(Enum):
    # Bit-wise operations
    bvnot = 1
    bvand = 2
    bvor = 3
    bvxor = 4
    # arthmetic operations
    bvneg = 5
    bvadd = 6
    bvsub = 7
    # shift operations
    bvshl = 8
    bvlshr = 9
    # concat
    concat = 10
    # extract
    extract = 11
    bvult = 16
    bvugt = 17
    bvuge = 18
    bvule = 19
    bvsgt = 20
    bvslt = 21
    bvsge = 22
    bvsle = 23
    bvmul = 12
    bvudiv = 13
    bvurem = 14
    bvsrem = 15


class bv:
    def __init__(self):
        self.length = 0
        # self.opt=None
        self.isBool = False
        self.name = ""


oneVarOp = [1, 5]
boolOutOp = [16, 17, 18, 19, 20, 21, 22, 23]
smallerOp = [11]
lagerOp = [10]


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
            self.output = bv()
            self.i = 0
            self.j = 0
            self.extend = 0

    def random_op(self):
        r = random.random()
        if r <= 0.1:
            rand = np.random.randint(16, 24)
        elif r > 0.9:
            rand = np.random.randint(12, 16)
        else:
            rand = np.random.randint(1, 10)
        return rand

    def gbv(self, length=256, isBool=False):
        bv_o = bv()
        bv_o.length = length
        # bv_o.opt=opnode
        bv_o.name = "bv_" + str(self.index)
        self.index = self.index + 1
        bv_o.isBool = isBool
        # bv_o.out=bv_o.name
        self.inlist.append(bv_o)
        return bv_o

    def gOut(self, node):
        node.output.name = "bv_" + str(self.index)
        self.index = self.index + 1
        if node.name_num in boolOutOp:
            node.output.length = 1
            node.output.isBool = True
        elif node.name == "concat":
            node.output.length = node.input[0].length + node.input[1].length
        elif node.name == "extract":
            node.output.length = node.j - node.i + 1
        else:
            node.output.length = node.input[0].length
            if (len(node.input) > 1):
                node.output.length = max(node.input[0].length, node.input[1].length)

    def addinput(self, vars_copy, pro=1):
        r = random.random()
        input = None
        if r <= 1:
            while len(vars_copy) > 0:
                rand = np.random.randint(0, len(vars_copy))
                var = vars_copy[rand]
                vars_copy.remove(var)
                if var.isBool == False:
                    input = var
                    break
        if input == None:
            input = self.gbv()
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
            input = self.gbv()
        return input

    def addnode(self, rand, isRandom, vars_copy):
        node = self.consop()
        # rand=self.random_op()
        node.name = opt(rand).name
        node.name_num = rand
        ##input
        if isRandom:
            input1 = self.addinput(vars_copy)
        else:
            input1 = self.addinput1(vars_copy)
        if node.name_num in smallerOp:
            node.i = random.randint(0, input1.length - 2)
            node.j = random.randint(node.i + 1, input1.length - 1)
        elif node.name_num not in oneVarOp:
            if isRandom:
                input2 = self.addinput(vars_copy)
            else:
                input2 = self.addinput1(vars_copy)
            if input1.length != input2.length and node.name_num not in lagerOp:
                node.extend = abs(input1.length - input2.length)
            node.input.append(input2)
        node.input.append(input1)
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

    def tosmt(self, filename):
        f = open(filename, "w")
        f.write("(set-logic QF_BV)\n")
        f.write("(set-option :produce-models true)\n")
        for i in range(len(self.inlist)):
            bv_o = self.inlist[i]
            f.write("(declare-const %s (_ BitVec %d))\n" % (bv_o.name, bv_o.length))
        for i in range(len(self.op)):
            output = self.op[i].output
            if self.op[i].name_num in boolOutOp:
                f.write("(declare-const %s Bool)\n" % (output.name))
            else:
                f.write("(declare-const %s (_ BitVec %d))\n" % (output.name, output.length))
        for i in range(len(self.op)):
            bvlist = self.op[i].input
            length = len(bvlist)
            output = self.op[i].output
            if length > 1: maxlength = max(bvlist[0].length, bvlist[1].length)
            if self.op[i].name == "extract":
                f.write("(assert (= %s ((_ %s %d %d) " % (output.name, self.op[i].name, self.op[i].j, self.op[i].i))
            else:
                f.write("(assert (= %s (%s " % (output.name, self.op[i].name))
            for j in range(length):
                tempname = bvlist[j].name
                if self.op[i].extend != 0 and bvlist[j].length < maxlength:
                    tempname = "((_ zero_extend {}) {})".format(self.op[i].extend, tempname)
                if j == length - 1:
                    f.write("%s)))\n" % tempname)
                else:
                    f.write("%s " % tempname)
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
            self.input1 = bv()
            self.input2 = bv()

    class gmop:
        def __init__(self):
            self.name = ""
            self.input = []  # znode
            self.output = ""

    def randopt(self):
        r = random.random()
        if r < 0.05:
            rand = 1
        elif r > 0.6:
            rand = 2
        else:
            rand = 3
        return rand

    def gznode(self, cons_copy):
        length = len(cons_copy)
        trytime = 0
        while length > 1 and trytime < 1000:
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
                cons_copy.remove(var1)
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
            if input1.name == "not" or input1.name == "and" or input1.name == "or":  # 如果是mnode
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
                if input1.name == "not" or input1.name == "and" or input1.name == "or":  # 如果是mnode
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
            if self.zlist[i].input1.length == self.zlist[i].input2.length:
                f.write("(assert (= %s (= %s %s)))\n" % (
                self.zlist[i].name, self.zlist[i].input1.name, self.zlist[i].input2.name))
            else:
                extend = abs(self.zlist[i].input1.length - self.zlist[i].input2.length)
                if self.zlist[i].input1.length > self.zlist[i].input2.length:
                    f.write("(assert (= %s (= %s ((_ zero_extend %s) %s))))\n" % (
                    self.zlist[i].name, self.zlist[i].input1.name, extend, self.zlist[i].input2.name))
                else:
                    f.write("(assert (= %s (= ((_ zero_extend %s) %s) %s)))\n" % (
                    self.zlist[i].name, extend, self.zlist[i].input1.name, self.zlist[i].input2.name))

        f.write("(assert ")
        f.write(self.modelop[-1].output)
        f.write(" )\n")
        f.write("(check-sat)\n")
        f.write("(get-model)\n")
        f.write("(exit)\n")
        f.close()


if __name__ == "__main__":
    # num=0
    # i=0
    # while(num<50):
    #     r=gmodel()
    #     r.modeltree(40,30)
    #     filename="SMT-bv1/seed_"+str(i)+".smt2"
    #     i=i+1
    #     r.tosmt(filename)
    #     filetime = z3_time.gtime(filename)
    #     print(filetime)
    #     if(filetime>60):
    #         mun=num+1
    #         f=open("SMT-bv1/hard_time.txt","a")
    #         f.write(filename+"\t"+str(filetime)+"\n")

    for i in range(100):
        filename = "SMT-test/seed_" + str(i) + ".smt2"
        r = gmodel()
        r.modeltree(i + 5, 10)
        r.tosmt(filename)
        filetime = z3_time.gtime(filename)
        print(filetime)

    # index=0
    # for i in range(4,1000):
    #     filename="SMT-generator/seeds_bv/seed_"+str(i)+".smt2"
    #     r=gmodel()
    #     r.modeltree(30,30)
    #     r.tosmt(filename)
    #     filetime=z3_time.gtime(filename)
    #     print(filetime)
    #     f=open("SMT-generator/bv_time.txt","a")
    #     f.write(filename+"\t"+str(filetime)+"\n")
