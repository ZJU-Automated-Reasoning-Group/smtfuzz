import random

cvc_regular_options = [
    # "ackermann",
    "arrays-eager-index",
    # "bitblast=MODE",
    "bitwise-eq",
    # "block-models=MODE",
    # "bool-to-bv=MODE",
    "bv-alg-extf",
    # "bv-eq-slicer=MODE",
    "bv-eq-solver", "bv-inequality-solver",
    # "bv-sat-solver=MODE",
    "bv-to-bool", "cegqi", "cegqi-bv",
    # "cegqi-bv-ineq=MODE",
    "cegqi-innermost", "cegqi-midpoint", "cegqi-nested-qe",
    # "cegis-sample=MODE",
    "sygus-si-abort",
    "e-matching", "ext-rew-prep", "ext-rewrite-quant", "finite-model-find",
    "fs-interleave", "full-saturate-quant",
    # "full-saturate-quant-limit=N",
    "ho-elim", "ho-elim-store-ax",
    # "inst-format=MODE",
    "inst-no-entail",
    # "inst-when=MODE",
    "macros-quant",
    # "macros-quant-mode=MODE",
    "mbqi-one-inst-per-round",
    "miniscope-quant", "miniscope-quant-fv",
    # "model-cores=MODE",
    "multi-trigger-cache", "multi-trigger-linear",
    "multi-trigger-priority", "multi-trigger-when-single",
    "new-prop",
    "nl-ext-tf-tplanes", "nl-ext-tplanes", "nl-ext-tplanes-interleave",
    "pre-skolem-quant",
    # "prenex-quant=MODE",
    "qcf-all-conflict",
    "quant-alpha-equiv", "quant-cf",
    # "quant-cf-mode=MODE
    "re-elim", "re-elim-agg",
    # "re-inter-mode=MODE",
    "relevant-triggers",
    "sets-ext",
    "solve-real-as-int",
    # "sort-inference",
    "static-learning", "stats-hide-zeros",
    "strict-triggers",
    "strings-exp", "strings-fmf", "strings-lazy-pp",
    "sygus-add-const-grammar", "sygus-pbe",
    "uf-ho", "uf-ss-fair",
]


def mutate_cvc4_option(f):
    tf = ['true', 'false']
    ss = random.choice(cvc_regular_options)
    f.write('(set-option :{} {})\n'.format(ss, random.choice(tf)))
