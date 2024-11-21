import random

from generator import generate_from_grammar_as_str

from cvc4option_mutator import mutate_cvc4_option
from examples.mutators.z3option_mutator import mutate_z3_option

# import timeout_decorator

# currently only supports Bool_Op
mutation_trick = {
    # "<":
    #         [">", "<=", ">=", "="],
    # ">":
    #        ["<", "<=", ">=", "="],
    "<=":
        ["<", ">", ">=", "="],
    ">=":
        ["<", "<=", ">", "="],

    # "=":
    #        ["distinct"],

    "distinct":
        ["="],

    "and":
        ["or"],

    "or":
        ["and"],

    "=>":
        ["and", "or"],

    "bvule":
        ["bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"],

    "bvuge":
        ["bvugt", "bvule", "bvslt", "bvsle", "bvsgt", "bvsge"],

    "bvslt":
        ["bvugt", "bvuge", "bvule", "bvsle", "bvsgt", "bvsge"],

    "bvsle":
        ["bvugt", "bvuge", "bvslt", "bvule", "bvsgt", "bvsge"],

    "bvsgt":
        ["bvugt", "bvuge", "bvslt", "bvsle", "bvule", "bvsge"],

    "str.<":
        ["str.<=", "str.prefixof", "str.suffixof", "str.contains"],

    "str.<=":
        ["str.<", "str.prefixof", "str.suffixof", "str.contains"],

    "str.suffixof":
        ["str.<=", "str.prefixof", "str.<", "str.contains"],

    "str.prefixof":
        ["str.<", "str.<=", "str.suffixof", "str.contains"],

    "str.contains":
        ["str.<", "str.<=", "str.suffixof", "str.prefixof"],

}

mutation_int = {
    # "+":
    #         ["-"],

    "*":
        ["+", "-"],

    "mod":
        ["div"],

    "div":
        ["mod"],

    "abs":
        ["-"],

    "fp.isPositive":
        ['fp.isPositive', 'fp.isNormal', 'fp.isNegative', 'fp.isNaN', 'fp.isSubnormal', 'fp.isInfinite', 'fp.isZero'],
    "fp.isNormal":
        ['fp.isPositive', 'fp.isNormal', 'fp.isNegative', 'fp.isNaN', 'fp.isSubnormal', 'fp.isInfinite', 'fp.isZero'],
    "fp.isNegative":
        ['fp.isPositive', 'fp.isNormal', 'fp.isNegative', 'fp.isNaN', 'fp.isSubnormal', 'fp.isInfinite', 'fp.isZero'],
    "fp.isNaN":
        ['fp.isPositive', 'fp.isNormal', 'fp.isNegative', 'fp.isNaN', 'fp.isSubnormal', 'fp.isInfinite', 'fp.isZero'],
    "fp.isSubnormal":
        ['fp.isPositive', 'fp.isNormal', 'fp.isNegative', 'fp.isNaN', 'fp.isSubnormal', 'fp.isInfinite', 'fp.isZero'],
    "fp.isInfinite":
        ['fp.isPositive', 'fp.isNormal', 'fp.isNegative', 'fp.isNaN', 'fp.isSubnormal', 'fp.isInfinite', 'fp.isZero'],
    "fp.isZero":
        ['fp.isPositive', 'fp.isNormal', 'fp.isNegative', 'fp.isNaN', 'fp.isSubnormal', 'fp.isInfinite', 'fp.isZero'],

    "fp.leq":
        ['fp.lt', 'fp.eq', 'fp.geq', 'fp.gt'],
    "fp.lt":
        ['fp.leq', 'fp.eq', 'fp.geq', 'fp.gt'],
    "fp.eq":
        ['fp.leq', 'fp.lt', 'fp.geq', 'fp.gt'],
    "fp.geq":
        ['fp.leq', 'fp.lt', 'fp.eq', 'fp.gt'],
    "fp.gt":
        ['fp.leq', 'fp.lt', 'fp.eq', 'fp.geq'],

}

mutation_real = {
    "+":
        ["-"],
}

mutation_bv = {
    "bvand":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],

    "bvor":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvnand":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvnor":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvxor":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvsub":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvsdiv":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvsmod":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvadd":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvmul":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvudiv":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvurem":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvshl":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvlshr":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
    "bvashr":
        ["bvand", "bvor", "bvnand", "bvnor", "bvxor", "bvsub", "bvsdiv", "bvsmod", "bvadd", "bvmul", "bvudiv", "bvurem",
         "bvshl", "bvlshr", "bvashr"],
}

mutation_set = {
    "union":
        ["union", "intersection", "setminus"],

    "intersection":
        ["union", "intersection", "setminus"],

    "setminus":
        ["union", "intersection", "setminus"],

}

mutation_re = {
    "re.comp":
        ["re.+", "re.opt", "re.*"],
    "re.+":
        ["re.comp", "re.opt", "re.*"],
    "re.opt":
        ["re.comp", "re.+", "re.*"],
    "re.*":
        ["re.comp", "re.+", "re.opt"]
}
mutation_fp = {
    "RNE":
        ["RNA", "RTP", "RTN", "RTZ"],
    "RNA":
        ["RNA", "RTP", "RTN", "RTZ"],
    "RTP":
        ["RNE", "RNA", "RTN", "RTZ"],
    "RTN":
        ["RNE", "RNA", "RTP", "RTZ"],
    "RTZ":
        ["RNE", "RNA", "RTP", "RTN"]

}


class Generator:
    def __init__(self, seeds):
        self.seeds = seeds

    def generate(self):
        pass


def get_script_from_file(file):
    final = []
    with open(file, "r") as reader:
        script = reader.readlines()
    for l in script:
        if not (l.startswith('(get-op') or l.startswith('(exit')):
            final.append(l)
    # print(final)
    return final


class StringMutation(Generator):

    def __init__(self, seed):
        self.success = False
        self.formula = []
        self.read_formula(seed)

        self.unsat_core = False
        self.proof = False
        self.smtopt = False

        self.z3option = False
        self.cvc4option = False

        self.pure_option_mode = False

    def read_formula(self, seed):
        self.formula = get_script_from_file(seed)
        self.success = True

    def enable_unsat_core(self):
        self.unsat_core = True

    def enable_proof(self):
        self.proof = True

    def enable_z3_option(self):
        self.z3option = True

    def enable_cvc4_option(self):
        self.cvc4option = True

    def enable_smtopt(self):
        self.smtopt = True

    def mutate_line(self, to_mutate):
        m_dynamic_mutate_bool = True
        m_dynamic_mutate_bv = True
        m_dynamic_mutate_int = True
        m_dynamic_mutate_set = True
        m_dynamic_mutate_fp = True
        mut_rate_swam = [0.11, 0.22, 0.33, 0.44, 0.55]
        mut_rate = random.choice(mut_rate_swam)
        new_str = to_mutate

        if random.random() < mut_rate:
            cnt = new_str.split("(assert")[1]
            new_str = "(assert (not " + cnt + ")"

        if m_dynamic_mutate_bool and random.random() < mut_rate:
            mutant_operators = mutation_trick.keys()
            for m in mutant_operators:
                if m in to_mutate:
                    new_str = new_str.replace(m, random.choice(mutation_trick[m]), 1)
                    break

        if m_dynamic_mutate_bv and random.random() < mut_rate:
            mutant_operators = mutation_bv.keys()
            for m in mutant_operators:
                if m in to_mutate:
                    new_str = new_str.replace(m, random.choice(mutation_bv[m]), 1)
                    break

        if m_dynamic_mutate_int and random.random() < mut_rate:
            mutant_operators = mutation_int.keys()
            for m in mutant_operators:
                if m in to_mutate:
                    new_str = new_str.replace(m, random.choice(mutation_int[m]), 1)
                    break

        if m_dynamic_mutate_set and random.random() < mut_rate:
            mutant_operators = mutation_set.keys()
            for m in mutant_operators:
                if m in to_mutate:
                    new_str = new_str.replace(m, random.choice(mutation_set[m]), 1)
                    break

        if m_dynamic_mutate_fp and random.random() < mut_rate:
            mutant_operators = mutation_fp.keys()
            for m in mutant_operators:
                if m in to_mutate:
                    new_str = new_str.replace(m, random.choice(mutation_fp[m]), 1)
                    break

        return new_str

    def generate(self, output):
        if not self.success: return False

        if self.pure_option_mode:
            with open(output, "w") as f:
                if self.z3option: mutate_z3_option(f)
                if self.cvc4option: mutate_cvc4_option(f)

                if self.unsat_core: f.write("(set-option :produce-unsat-cores true)\n")
                if self.proof: f.write("(set-option :produce-proofs true)\n")
                opt_added = False
                for j in range(len(self.formula)):
                    line = self.formula[j]
                    if opt_added == False and (line.startswith("(dec") or line.startswith("(set-lo")):
                        opt_added = True
                    f.write(line)
                f.close()

                return self.success

        try:
            with open(output, 'w') as mut:
                if self.z3option: mutate_z3_option(mut)
                if self.cvc4option: mutate_cvc4_option(mut)

                if self.unsat_core: mut.write("(set-option :produce-unsat-cores true)\n")
                if self.proof: mut.write("(set-option :produce-proofs true)\n")
                if self.smtopt:  # for z3
                    pri = random.random()
                    if pri < 0.33:
                        mut.write('(set-option :opt.priority lex)\n')
                    elif pri < 0.66:
                        mut.write('(set-option :opt.priority pareto)\n')
                    else:
                        mut.write('(set-option :opt.priority box)\n')

                if False:
                    pred = generate_from_grammar_as_str()
                    if pred != False:
                        mut.write(pred)
                        mut.write("\n")
                        mut.write('(reset)\n')

                opt_added = False
                for j in range(len(self.formula)):
                    line = self.formula[j]
                    if opt_added == False and (line.startswith("(dec") or line.startswith("(set-lo")):
                        opt_added = True
                    # for Sygus: constraint
                    if (line.startswith("(assert") or line.startswith("(constraint")) and random.random() <= 0.1:
                        line = self.mutate_line(line)
                    mut.write(line)
                # if self.z3option: mutate_z3_tactic(mut)
                mut.close()
                return self.success
        except Exception as e:
            self.success = False
            return False
