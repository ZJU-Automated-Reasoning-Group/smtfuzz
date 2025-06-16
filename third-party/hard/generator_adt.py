from enum import Enum
import numpy as np
import random
import z3_other
import z3_time


class opt(Enum):
    # Constructor operations
    mk_cons = 1         # constructor application
    # Selector operations  
    sel_head = 2        # head selector
    sel_tail = 3        # tail selector
    sel_first = 4       # first selector
    sel_second = 5      # second selector
    # Tester operations
    is_cons = 6         # is-cons tester
    is_nil = 7          # is-nil tester
    is_pair = 8         # is-pair tester
    # Equality
    adt_eq = 9          # =
    adt_neq = 10        # distinct


class adt:
    def __init__(self):
        self.isBool = False
        self.name = ""
        self.adt_type = "List"  # List, Pair, Tree, etc.
        self.element_type = "Int"  # Int, Bool, etc.


oneVarOp = [2, 3, 4, 5, 6, 7, 8]  # selectors and testers
boolOutOp = [6, 7, 8, 9, 10]  # testers and equality
constructorOp = [1]  # constructor operations
twoVarOp = [1, 9, 10]  # constructor and equality operations


class gconstrains:
    def __init__(self):
        self.op = []
        self.index = 0
        self.outlist = []
        self.inlist = []
        self.adt_types = ["List", "Pair", "Tree"]
        self.element_types = ["Int", "Bool"]
        self.declared_types = set()

    class consop:
        def __init__(self):
            self.name = ""
            self.name_num = 0
            self.input = []
            self.output = adt()
            self.constructor_name = ""
            self.selector_name = ""

    def random_op(self):
        r = random.random()
        if r <= 0.3:
            rand = np.random.randint(1, 2)   # constructor
        elif r <= 0.7:
            rand = np.random.randint(2, 6)   # selectors
        else:
            rand = np.random.randint(6, 11)  # testers and equality
        return rand

    def getopt(self, key):
        operations = {
            1: "mk-cons", 2: "head", 3: "tail", 4: "first", 5: "second",
            6: "is-cons", 7: "is-nil", 8: "is-pair", 9: "=", 10: "distinct"
        }
        return operations.get(key, "unknown")

    def gadt(self, isBool=False, adt_type="List", element_type="Int"):
        adt_o = adt()
        adt_o.name = "adt_" + str(self.index)
        self.index = self.index + 1
        adt_o.isBool = isBool
        adt_o.adt_type = adt_type
        adt_o.element_type = element_type
        self.inlist.append(adt_o)
        return adt_o

    def gOut(self, node):
        node.output.name = "adt_" + str(self.index)
        self.index = self.index + 1
        
        if node.name_num in boolOutOp:
            node.output.isBool = True
        else:
            node.output.isBool = False
            # Inherit type from input for selectors
            if len(node.input) > 0:
                node.output.adt_type = node.input[0].adt_type
                node.output.element_type = node.input[0].element_type

    def addinput(self, adts_copy, need_specific_type=None):
        r = random.random()
        input_var = None
        
        if r <= 0.8:  # Try to use existing variables
            while len(adts_copy) > 0:
                rand = np.random.randint(0, len(adts_copy))
                var = adts_copy[rand]
                adts_copy.remove(var)
                
                if need_specific_type and var.adt_type == need_specific_type and not var.isBool:
                    input_var = var
                    break
                elif not need_specific_type and not var.isBool:
                    input_var = var
                    break
        
        # Create new variable if needed
        if input_var == None:
            adt_type = need_specific_type if need_specific_type else random.choice(self.adt_types)
            element_type = random.choice(self.element_types)
            input_var = self.gadt(adt_type=adt_type, element_type=element_type)
        
        return input_var

    def addinput1(self, adts_copy, need_specific_type=None):
        input_var = None
        while len(adts_copy) > 0:
            var = adts_copy[-1]
            adts_copy.remove(var)
            
            if need_specific_type and var.adt_type == need_specific_type and not var.isBool:
                input_var = var
                break
            elif not need_specific_type and not var.isBool:
                input_var = var
                break
        
        if input_var == None:
            adt_type = need_specific_type if need_specific_type else random.choice(self.adt_types)
            element_type = random.choice(self.element_types)
            input_var = self.gadt(adt_type=adt_type, element_type=element_type)
        
        return input_var

    def addnode(self, rand, isRandom, adts_copy):
        node = self.consop()
        node.name = self.getopt(rand)
        node.name_num = rand
        
        # Handle different operation types
        if rand == 1:  # mk-cons constructor
            if isRandom:
                # For List: cons needs element and list
                input1 = self.gadt(element_type=random.choice(self.element_types))  # element
                input2 = self.addinput(adts_copy, need_specific_type="List")  # list
            else:
                input1 = self.gadt(element_type=random.choice(self.element_types))
                input2 = self.addinput1(adts_copy, need_specific_type="List")
            node.input.extend([input1, input2])
            node.constructor_name = "cons"
        elif rand in [2, 3]:  # head, tail - need List
            if isRandom:
                input1 = self.addinput(adts_copy, need_specific_type="List")
            else:
                input1 = self.addinput1(adts_copy, need_specific_type="List")
            node.input.append(input1)
        elif rand in [4, 5]:  # first, second - need Pair
            if isRandom:
                input1 = self.addinput(adts_copy, need_specific_type="Pair")
            else:
                input1 = self.addinput1(adts_copy, need_specific_type="Pair")
            node.input.append(input1)
        elif rand in [6, 7]:  # is-cons, is-nil - need List
            if isRandom:
                input1 = self.addinput(adts_copy, need_specific_type="List")
            else:
                input1 = self.addinput1(adts_copy, need_specific_type="List")
            node.input.append(input1)
        elif rand == 8:  # is-pair - need Pair
            if isRandom:
                input1 = self.addinput(adts_copy, need_specific_type="Pair")
            else:
                input1 = self.addinput1(adts_copy, need_specific_type="Pair")
            node.input.append(input1)
        elif rand in [9, 10]:  # equality operations
            if isRandom:
                input1 = self.addinput(adts_copy)
                input2 = self.addinput(adts_copy)
            else:
                input1 = self.addinput1(adts_copy)
                input2 = self.addinput1(adts_copy)
            node.input.extend([input1, input2])
        
        self.gOut(node)
        self.outlist.append(node.output)
        self.op.append(node)
        return node.output

    def gcons(self, number):
        for _ in range(number):
            rand = self.random_op()
            adts = self.inlist + self.outlist
            adts_copy = adts[:]
            self.addnode(rand, True, adts_copy)

    def generate_adt_declarations(self):
        declarations = []
        
        # Collect all ADT types used
        all_types = set()
        for var in self.inlist + self.outlist:
            if not var.isBool:
                all_types.add((var.adt_type, var.element_type))
        
        # Generate type declarations
        for adt_type, element_type in all_types:
            if adt_type == "List":
                declarations.append(f"(declare-datatypes ((List{element_type} 0)) (((nil) (cons (head {element_type}) (tail List{element_type})))))")
            elif adt_type == "Pair":
                declarations.append(f"(declare-datatypes ((Pair{element_type} 0)) (((pair (first {element_type}) (second {element_type})))))")
            elif adt_type == "Tree":
                declarations.append(f"(declare-datatypes ((Tree{element_type} 0)) (((leaf (value {element_type})) (node (left Tree{element_type}) (right Tree{element_type})))))")
        
        return declarations

    def tosmt(self, filename):
        f = open(filename, "w")
        f.write("(set-logic QF_DT)\n")
        f.write("(set-option :produce-models true)\n")
        
        # Generate ADT type declarations
        declarations = self.generate_adt_declarations()
        for decl in declarations:
            f.write(decl + "\n")
        
        # Declare input variables
        for i in range(len(self.inlist)):
            input_var = self.inlist[i]
            if input_var.isBool:
                f.write("(declare-const %s Bool)\n" % (input_var.name))
            else:
                type_name = f"{input_var.adt_type}{input_var.element_type}"
                f.write("(declare-const %s %s)\n" % (input_var.name, type_name))
        
        # Declare output variables
        for i in range(len(self.op)):
            output = self.op[i].output
            if self.op[i].name_num in boolOutOp:
                f.write("(declare-const %s Bool)\n" % (output.name))
            else:
                type_name = f"{output.adt_type}{output.element_type}"
                f.write("(declare-const %s %s)\n" % (output.name, type_name))
        
        # Generate assertions
        for i in range(len(self.op)):
            inputlist = self.op[i].input
            length = len(inputlist)
            output = self.op[i].output
            
            if self.op[i].name_num == 1:  # constructor
                f.write("(assert (= %s (cons " % (output.name))
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
            adt1 = cons_copy[rand1]
            rand2 = np.random.randint(0, length)
            adt2 = cons_copy[rand2]
            if adt1 != adt2 and adt1.isBool == adt2.isBool:
                z = self.znode()
                z.name = "z_" + str(self.zindex)
                self.zindex += 1
                z.input1 = adt1
                z.input2 = adt2
                self.zlist.append(z)
                cons_copy.remove(adt1)
                cons_copy.remove(adt2)
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