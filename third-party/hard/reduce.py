import readfile
import generator_bv
import generator_fp
import generator_real
import z3_time
import z3_other
import copy


class reduce_seed:
    def __init__(self, generator):
        self.generator = generator
        self.readfile = readfile.readfile(self.generator)

    def reduce_cons(self, cons, model):
        cur_cons = cons.op[-1]
        cons.op.remove(cur_cons)
        cons.outlist.remove(cur_cons.output)
        cur_z = None
        for node in model.zlist:
            if cur_cons.output == node.input1 or cur_cons.output == node.input2:
                cur_z = node
                break

        if cur_z:
            cur = cur_z
            model.zlist.remove(cur_z)
            for node in model.modelop:
                if cur in node.input and cur == cur_z:
                    if node.name == "not":
                        node.output = None
                    else:
                        node.name = "not"
                        node.input.remove(cur)
                        if node.input[-1].name == "not" or node.input[-1].name == "and" or node.input[-1].name == "or":
                            node.output = "( not " + node.input[-1].output + " )"
                        else:
                            node.output = "( not " + node.input[-1].name + " )"
                    cur = node
                elif cur in node.input:
                    input1 = node.input[0]
                    if node.name == "not":
                        if input1.name == "not" or input1.name == "and" or input1.name == "or":  # 如果是mnode
                            if input1.output:
                                node.output = "( not " + input1.output + " )"
                            else:
                                node.output = None
                        else:
                            node.output = "( not " + input1.name + " )"
                    else:
                        input2 = node.input[-1]
                        if input1.name == "not" or input1.name == "and" or input1.name == "or":
                            if input1.output:
                                input1 = input1.output
                            else:
                                input1 = None
                        else:
                            input1 = input1.name

                        if input2.name == "not" or input2.name == "and" or input2.name == "or":
                            if input2.output:
                                input2 = input2.output
                            else:
                                input2 = None
                        else:
                            input2 = input2.name

                        if input1 and input2:
                            node.output = "( " + node.name + " " + input1 + " " + input2 + " )"
                        elif input1:
                            node.name = "not"
                            node.output = "( not " + input1 + " )"
                        elif input2:
                            node.name = "not"
                            node.output = "( not " + input2 + " )"
                        else:
                            node.output = None
                    cur = node
        # print(seed.readfile.model.modelop[-1].output)


if __name__ == "__main__":
    for i in range(0, 50):
        filename = "SMT-real1/seed_" + str(i) + ".smt2"
        # filename="example1.smt2"
        seed = reduce_seed(generator_real)
        seed.readfile.readf(filename)
        filetime = 61
        f = open("reductionREAL1.txt1.txt", "a")
        f.write("------------------------------------------------------\n")
        f.write(filename + "\t" + str(filetime) + "\n")
        f.close()

        index = 0
        filename = filename.replace(".smt2", "")
        while True:
            aftername = filename + "_" + str(index) + ".smt2"
            index += 1
            seed.reduce_cons(seed.readfile.cons, seed.readfile.model)
            seed.readfile.model.tosmt(aftername)
            filetime = z3_time.gtime(aftername)
            f = open("reductionREAL1.txt", "a")
            f.write(aftername + "\t" + str(filetime) + "\n")
            f.close()
            print(aftername)
            if len(seed.readfile.model.zlist) <= 1:
                break
            seed = reduce_seed(generator_real)
            seed.readfile.readf(aftername)
