import random

cvc_string_regular_opt = [
   "--strings-exp",
   "--strings-fmf",
   "--strings-lazy-pp",
   "--strings-check-entail-len",
   "--strings-mbr",
   "--re-elim=on",
   "--re-inter-mode=all",
   "--strings-eager-eval",
   "--strings-eager-len-re",
   "--strings-eager-solver",
   "--strings-regexp-inclusion",
   "--sygus-inst"
]

def get_string_cvc_opt():
    opt = []
    for a in cvc_string_regular_opt:
        if a == "--sygus-inst":
            opt.append([a,'-q'])
        else:
            opt.append([a,'--incremental','-q'])
    return opt

z3_string_opt = [
    'smt.seq.validate=true',
    'nlsat.randomize=false',
    'smt.seq.split_w_len=false',
    'nlsat.shuffle_vars=true',
    'smt.arith.solver=2',
    'smt.arith.solver=1',
    'smt.arith.solver=3',
    'smt.arith.solver=4',
    'smt.arith.solver=5',
    'smt.arith.solver=6'
]

def get_string_z3_opt():
    opt = []
    for i in range(5):
        a = random.choice(z3_string_opt)
        opt.append([a])
    return opt

