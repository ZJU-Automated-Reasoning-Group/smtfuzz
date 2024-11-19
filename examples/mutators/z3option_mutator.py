import random

boolean_solver_options = ['smt.ematching', 'smt.quasi_macros', 'smt.arith.propagate_eqs',
                          'smt.arith.reflect', 'smt.arith.auto_config_simplex',
                          'smt.arith.bprop_on_pivoted_rows', 'smt.arith.greatest_error_pivot',
                          'smt.arith.int_eq_branch', 'smt.arith.min', 'smt.arith.random_initial_value', 'smt.dack.eq',
                          'smt.theory_aware_branching', 'smt.mbqi', 'smt.arith.eager_eq_axioms']

z3_str_options = ['smt.str.fixed_length_naive_cex', 'smt.str.aggressive_length_testing', 'smt.str.strong_arrangements',
                  'smt.str.string_constant_cache', 'smt.seq.split_w_len', 'smt.str.fast_length_tester_cache']
z3_str_options += ['smt.str.aggressive_unroll_testing', 'smt.str.aggressive_value_testing',
                   'smt.theory_aware_branching']

sat_solver_options = ['sat.abce', 'sat.acce', 'sat.anf', 'sat.cce', 'sat.asymm_branch.all', 'sat.bca', 'sat.bce',
                      'sat.branching.anti_exploration', 'sat.cut', 'sat.cut.aig', 'sat.cut.npn3', 'sat.force_cleanup',
                      'sat.elim_vars', 'sat.scc', 'sat.scc.tr']

nlsat_options = ['nlsat.factor', 'nlsat.inline_vars', 'nlsat.minimize_conflicts', 'nlsat.randomize',
                 'nlsat.shuffle_vars', 'nlsat.reorder']

# for internel use: 'nlsat.log_lemmas', 'nlsat.check_lemmas'
model_maker_options = ['model.inline_def', 'model.partial', 'model.completion']
model_maker_options += ['model.compact']

# algebraic.factor
rewriter_options = ['rewriter.bit2bool', 'rewriter.mul_to_power', 'tactic.solve_eqs.theory_solver',
                    'rewriter.expand_nested_stores',
                    'rewriter.ite_extra_rules', 'rewriter.push_ite_arith', 'rewriter.push_to_real',
                    'rewriter.sort_sums', 'rewriter.elim_and', 'rewriter.eq2ineq', 'rewriter.local_ctx',
                    'rewriter.split_concat_eq', 'rewriter.arith_ineq_lhs', 'rewriter.flat', 'rewriter.arith_lhs',
                    'rewriter.blast_distinct', 'rewriter.blast_eq_value', 'rewriter.bv_sort_ac', 'rewriter.bv_le_extra',
                    'rewriter.cache_all']

numural_options = ['smt.phase_selection', 'smt.threads', 'smt.arith.solver', 'smt.random_seed']
numural_options += ['parallel.simplify.inprocess.max', 'parallel.conquer.delay', 'parallel.simplify.exp']


def mutate_z3_tactic(f):
    z3_middle_tactics = [
        'aig ',
        'solve-eqs ',
        'horn-simplify '
        'subpaving ',
        'ackermannize_bv ',
        'reduce-bv-size ',
        'macro-finder ',
        'ufbv-rewriter ',
        'reduce-invertible ',
        'add-bounds ',
        'fix-dl-var ',
        'unit-subsume-simplify ',
        'normalize-bounds ',
        'purify-arith ',
        'dom-simplify ',
        'propagate-bv-bounds-new '
        'ctx-solver-simplify ',
        # 'solve-eqs ',
    ]
    z3_final_tactics = ['qfnia ', 'aufnira ', 'qfufbv_ackr ', 'qffd ', 'smt ']
    z3_final_tactics += ['bv ', 'nra ', 'uflra ', 'lira ', 'ufbv ', 'nlsat ', 'qe2 ']
    if random.random() < 0.5: z3_middle_tactics += z3_final_tactics

    checkcmd = "\n(check-sat-using (then simplify "
    l = random.randint(0, len(z3_middle_tactics))
    to_set = random.sample(z3_middle_tactics, l)
    for tac in to_set:
        checkcmd += tac
    final_t = z3_final_tactics[random.randint(0, len(z3_final_tactics) - 1)] + "))"
    checkcmd += final_t
    f.write(checkcmd)


def mutate_z3_option(f):
    tf = ['true', 'false']
    if random.random() < 0.5:
        if random.random() < 0.5:
            f.write("(set-option :ackermannization.sat_backend true)\n")
        else:
            f.write("(set-option :ackermannization.inc_sat_backend true)\n")

    if random.random() < 0.2: f.write("(set-option :smt.quasi_macros true)\n")

    if random.random() < 0.05: f.write("(set-option :combined_solver.ignore_solver1 true)\n")

    l = random.randint(0, len(boolean_solver_options))
    to_set = random.sample(boolean_solver_options, l)
    for ss in to_set:
        f.write('(set-option :{} {})\n'.format(ss, random.choice(tf)))

    if True:
        l2 = random.randint(0, len(sat_solver_options))
        to_set2 = random.sample(sat_solver_options, l2)
        for i in to_set2:
            f.write('(set-option :{} {})\n'.format(i, random.choice(tf)))
        sat_branch = random.random()
        if sat_branch < 0.45:
            f.write('(set-option :sat.branching.heuristic vsids)\n')
        else:
            f.write('(set-option :sat.branching.heuristic chb)\n')
        if False:
            local_search_prob = random.random()
            if local_search_prob < 0.2:
                f.write('(set-option :sat.prob_search true)\n')
            elif local_search_prob < 0.5:
                f.write('(set-option :sat.local_search true)\n')
                f.write('(set-option :sat.cardinality.solver true)\n')

    l3 = random.randint(0, len(rewriter_options))
    to_set3 = random.sample(rewriter_options, l3)
    for ss in to_set3:
        f.write('(set-option :{} {})\n'.format(ss, random.choice(tf)))

    # l4 = random.randint(0, len(model_maker_options))
    # to_set4 = random.sample(model_maker_options, l4)
    # for ss in to_set4:
    #    f.write('(set-option :{} {})\n'.format(ss, random.choice(tf)))

    to_set5 = nlsat_options
    for i in to_set5:
        f.write('(set-option :{} {})\n'.format(i, random.choice(tf)))

    l6 = random.randint(0, len(numural_options))
    to_set6 = random.sample(numural_options, l6)
    for i in to_set6:
        if i == "smt.arith.solver":  # can set 6?
            if random.random() < 0.5:
                solid = 2
            else:
                solid = 6
            f.write('(set-option :{} {})\n'.format(i, solid))
        elif i == "smt.random_seed":
            f.write('(set-option :{} {})\n'.format(i, random.randint(0, 10)))
        elif i == "smt.phase_selection":
            f.write('(set-option :{} {})\n'.format(i, random.randint(0, 7)))
        elif i == "smt.threads":
            if random.random() < 0.3:
                f.write('(set-option :smt.threads 1)\n')
            else:
                f.write('(set-option :{} {})\n'.format(i, random.randint(2, 6)))
        elif i.startswith("para"):
            f.write('(set-option :{} {})\n'.format(i, random.randint(1, 8)))
        else:
            f.write('(set-option :{} {})\n'.format(i, random.randint(1, 3)))

    if "smt.arith.solver" not in to_set6:
        if random.random() < 0.5:
            solid = 2
        else:
            solid = 6
        f.write('(set-option :smt.arith.solver {})\n'.format(solid))

    if random.random() < 0.5:
        f.write('(set-option :smt.core.minimize true)\n')

    l = random.randint(0, len(z3_str_options))
    to_set = random.sample(z3_str_options, l)
    for i in to_set:
        f.write('(set-option :{} {})\n'.format(i, random.choice(tf)))

    # case split
    if False:
        solid = random.randint(0, 6)
        f.write('(set-option :auto_config false)\n')
        f.write('(set-option :smt.case_split {})\n'.format(solid))
