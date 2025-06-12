
def cvc5_candidate_option(theory, mode):
    common = [' --abstract-values', ' --ackermann', ' --early-ite-removal', ' --expand-definitions', ' --ext-rew-prep=use',
              ' --ext-rew-prep=agg', ' --foreign-theory-rewrite', ' --ite-simp', ' --learned-rewrite',
              ' --model-witness-value', ' --on-repeat-ite-simp', ' --produce-abducts', ' --produce-assignments',
              ' --produce-difficulty', ' --produce-proofs', ' --produce-unsat-assumptions', ' --produce-unsat-cores',
              ' --repeat-simp', ' --simp-ite-compress', ' --simp-with-care', ' --solve-real-as-int',
              ' --sort-inference',
              ' --static-learning', ' --unconstrained-simp', ' --proof-alethe-res-pivots', ' --proof-annotate',
              ' --proof-pp-merge', ' --proof-print-conclusion', ' --proof-prune-input', ' --minisat-dump-dimacs',
              ' --minisat-elimination', ' --ag-miniscope-quant', ' --cegqi', ' --cegqi-all',
              ' --cegqi-bv', ' --cegqi-bv-concat-inv', ' --cegqi-bv-interleave-value', ' --cegqi-bv-linear',
              ' --cegqi-bv-rm-extract', ' --cegqi-bv-solve-nl', ' --cegqi-full', ' --cegqi-innermost',
              ' --cegqi-midpoint', ' --cegqi-min-bounds', ' --cegqi-model', ' --cegqi-multi-inst', ' --cegqi-nested-qe',
              ' --cegqi-nopt', ' --cegqi-repeat-lit', ' --cegqi-round-up-lia', ' --cegqi-sat', ' --cegqi-use-inf-int',
              ' --cegqi-use-inf-real', ' --cond-var-split-agg-quant', ' --cond-var-split-quant',
              ' --conjecture-filter-active-terms', ' --conjecture-filter-canonical', ' --conjecture-filter-model',
              ' --conjecture-gen', ' --conjecture-gen-uee-intro', ' --conjecture-no-filter', ' --cons-exp-triggers',
              ' --dt-stc-ind', ' --dt-var-exp-quant', ' --e-matching', ' --elim-taut-quant', ' --ext-rewrite-quant',
              ' --finite-model-find', ' --fmf-bound', ' --fmf-bound-int', ' --fmf-bound-lazy', ' --fmf-fmc-simple',
              ' --fmf-fresh-dc', ' --fmf-fun', ' --fmf-fun-rlv', ' --fmf-inst-engine', ' --fs-interleave',
              ' --fs-stratify', ' --fs-sum', ' --full-saturate-quant', ' --full-saturate-quant-rd', ' --global-negate',
              ' --ho-elim', ' --ho-elim-store-ax', ' --ho-matching', ' --ho-matching-var-priority',
              ' --ho-merge-term-db', ' --increment-triggers', ' --inst-level-input-only', ' --inst-no-entail',
              ' --inst-when-strict-interleave', ' --inst-when-tc-first', ' --int-wf-ind', ' --ite-dtt-split-quant',
              ' --macros-quant', ' --mbqi-interleave', ' --mbqi-one-inst-per-round', ' --miniscope-quant',
              ' --miniscope-quant-fv', ' --multi-trigger-cache', ' --multi-trigger-linear', ' --multi-trigger-priority',
              ' --multi-trigger-when-single', ' --partial-triggers', ' --pool-inst', ' --pre-skolem-quant',
              ' --pre-skolem-quant-agg', ' --pre-skolem-quant-nested', ' --prenex-quant-user', ' --purify-triggers',
              ' --qcf-all-conflict', ' --qcf-eager-check-rd', ' --qcf-eager-test', ' --qcf-nested-conflict',
              ' --qcf-skip-rd', ' --qcf-tconstraint', ' --qcf-vo-exp', ' --quant-alpha-equiv', ' --quant-cf',
              ' --quant-fun-wd', ' --quant-ind', ' --quant-split', ' --register-quant-body-terms',
              ' --relational-triggers', ' --relevant-triggers', ' --sygus', ' --sygus-add-const-grammar',
              ' --sygus-arg-relevant', ' --sygus-auto-unfold', ' --sygus-bool-ite-return-const',
              ' --sygus-core-connective', ' --sygus-crepair-abort', ' --sygus-eval-opt', ' --sygus-eval-unfold',
              ' --sygus-eval-unfold-bool', ' --sygus-ext-rew', ' --sygus-filter-sol-rev', ' --sygus-grammar-norm',
              ' --sygus-inference', ' --sygus-inst', ' --sygus-inv-templ-when-sg', ' --sygus-min-grammar',
              ' --sygus-pbe', ' --sygus-pbe-multi-fair', ' --sygus-qe-preproc', ' --sygus-query-gen-check',
              ' --sygus-rec-fun', ' --sygus-repair-const', ' --sygus-rr', ' --sygus-rr-synth',
              ' --sygus-rr-synth-accel',
              ' --sygus-rr-synth-check', ' --sygus-rr-synth-filter-cong', ' --sygus-rr-synth-filter-match',
              ' --sygus-rr-synth-filter-nl', ' --sygus-rr-synth-filter-order', ' --sygus-rr-synth-input',
              ' --sygus-rr-synth-input-use-bool', ' --sygus-rr-synth-rec', ' --sygus-rr-verify',
              ' --sygus-rr-verify-abort', ' --sygus-sample-fp-uniform', ' --sygus-sample-grammar', ' --sygus-si-abort',
              ' --sygus-stream', ' --sygus-templ-embed-grammar', ' --sygus-unif-cond-independent-no-repeat-sol',
              ' --sygus-unif-shuffle-cond', ' --term-db-cd', ' --var-elim-quant', ' --var-ineq-elim-quant']
    regular = ['--ackermann', '--arith-rewrite-equalities', '--bitblast=eager', '--bool-to-bv=all', '--bool-to-bv=ite',
               '--bv-print-consts-as-indexed-symbols', '--bv-solver=bitblast-internal', '--bv-to-bool',
               '--cbqi-all-conflict', '--cbqi-mode=conflict', '--cegis-sample=trust', '--cegis-sample=use', '--cegqi',
               '--cegqi-bv-ineq=keep', '--cegqi-inf-int', '--cegqi-inf-real', '--cegqi-midpoint', '--cegqi-nested-qe',
               '--check-interpolants', '--check-proofs', '--check-synth-sol', '--check-unsat-cores', '--decision=justification',
               '--decision=stoponly',  '--enum-inst', '--enum-inst-interleave', '--enum-inst-sum', '--ext-rew-prep=agg',
               '--ext-rew-prep=use', '--ext-rewrite-quant', '--finite-model-find', '--fmf-bound', '--fmf-fun', '--fmf-fun-rlv',
               '--full-saturate-quant', '--ho-elim', '--inst-when=full', '--inst-when=full-delay', '--inst-when=full-delay-last-call',
               '--inst-when=last-call', '--interpolants-mode=default', '--interpolants-mode=assumptions', '--interpolants-mode=conjecture',
               '--interpolants-mode=shared', '--interpolants-mode=all',  '--cegqi-bv-ineq=eq-slack', '--check-abducts',
               '--ite-lift-quant=all', '--ite-lift-quant=none', '--learned-rewrite', '--macros-quant', '--macros-quant-mode=all',
               '--macros-quant-mode=ground', '--mbqi-one-inst-per-round', '--miniscope-quant=off', '--miniscope-quant=conj',
               '--miniscope-quant=fv', '--miniscope-quant=agg', '--multi-trigger-cache', '--multi-trigger-priority',
               '--nl-ext-tplanes-interleave', '--nl-ext=none', '--nl-ext=light', '--no-arith-brab', '--nl-cov',
               '--no-arrays-eager-index', '--no-bitwise-eq', '--no-cbqi', '--no-cegqi-bv', '--no-cegqi-innermost',
               '--no-dt-share-sel', '--no-e-matching', '--no-elim-taut-quant', '--no-ho-elim-store-ax', '--no-inst-no-entail',
               '--no-multi-trigger-linear', '--no-nl-ext-factor', '--no-nl-ext-rewrite', '--no-nl-ext-tf-tplanes',
               '--no-nl-ext-tplanes', '--no-print-inst-full', '--no-produce-assertions', '--no-quant-alpha-equiv',
               '--no-static-learning', '--no-strings-check-entail-len', '--no-strings-eager-eval', '--no-strings-eager-solver',
               '--no-strings-lazy-pp', '--no-strings-mbr', '--no-strings-regexp-inclusion', '--no-sygus-add-const-grammar',
               '--no-sygus-min-grammar', '--no-sygus-pbe', '--no-sygus-sym-break-pbe', '--no-uf-ss-fair', '--no-var-elim-quant',
               '--no-var-ineq-elim-quant', '--pre-skolem-quant=agg', '--pre-skolem-quant=on', '--prenex-quant-user',
               '--prenex-quant=none', '--print-unsat-cores-full', '--produce-abducts', '--produce-assignments', '--produce-difficulty',
               '--produce-interpolants', '--produce-learned-literals', '--produce-proofs', '--produce-unsat-assumptions',
               '--produce-unsat-cores', '--quant-dsplit=agg', '--quant-dsplit=none', '--re-elim=agg', '--re-elim=on',
               '--multi-trigger-when-single', '--relevant-triggers', '--sets-ext', '--solve-real-as-int', '--simplification=none',
               '--sort-inference', '--static-learning', '--strings-deq-ext', '--strings-eager-len-re', '--strings-exp',
               '--strings-fmf', '--strings-process-loop-mode=none', '--sygus', '--sygus-core-connective',
               '--sygus-enum=random', '--sygus-enum=smart', '--sygus-enum=fast', '--sygus-enum=var-agnostic',
               '--sygus-eval-unfold=none', '--sygus-eval-unfold=single', '--sygus-eval-unfold=multi', '--sygus-fair=none',
               '--sygus-fair=direct', '--sygus-fair=dt-height-bound', '--sygus-fair=dt-size-bound', '--prenex-quant=norm',
               '--sygus-grammar-cons=any-term-concise', '--sygus-grammar-cons=any-const', '--sygus-grammar-cons=any-term',
               '--sygus-inst', '--sygus-inv-templ=none', '--sygus-inv-templ=pre', '--sygus-out=status',
               '--sygus-out=status-and-def', '--sygus-repair-const', '--sygus-rewriter=none', '--sygus-rewriter=basic',
               '--sygus-si-abort', '--sygus-si-rcons=none', '--sygus-si-rcons=try', '--sygus-si-rcons=all-limit',
               '--sygus-si=all', '--sygus-si=use', '--sygus-simple-sym-break=none', '--sygus-simple-sym-break=basic',
               '--sygus-stream', '--sygus-unif-pi=cond-enum-igain', '--sygus-unif-pi=complete', '--sygus-unif-pi=cond-enum',
               '--term-db-mode=relevant', '--trigger-sel=all', '--trigger-sel=max', '--trigger-sel=min-s-max', '--trigger-sel=min-s-all',
               '--uf-lazy-ll', '--uf-ss=none', '--uf-ss=no-minimal', '--unconstrained-simp']
    unique = []
    if theory in ["int", "real"]:
        unique = [' --arith-brab', ' --arith-cong-man', ' --arith-eq-solver', ' --arith-no-partial-fun',
                  ' --arith-rewrite-equalities', ' --collect-pivot-stats', ' --cut-all-bounded', ' --dio-decomps',
                  ' --dio-solver', ' --fc-penalties', ' --lemmas-on-replay-failure', ' --miplib-trick', ' --new-prop',
                  ' --nl-cad', ' --nl-cad-prune', ' --nl-cad-var-elim', ' --nl-ext-ent-conf', ' --nl-ext-factor',
                  ' --nl-ext-inc-prec', ' --nl-ext-purify', ' --nl-ext-rbound', ' --nl-ext-rewrite',
                  ' --nl-ext-split-zero', ' --nl-ext-tf-tplanes', ' --nl-ext-tplanes', ' --nl-ext-tplanes-interleave',
                  ' --nl-icp', ' --nl-rlv-assert-bounds', ' --pb-rewrites', ' --restrict-pivots',
                  ' --revert-arith-models-on-unsat', ' --se-solve-int', ' --soi-qe', ' --use-approx',
                  ' --use-fcsimplex',
                  ' --use-soi']
    elif theory == "array":
        unique = [' --arrays-eager-index', ' --arrays-eager-lemmas', ' --arrays-exp', ' --arrays-optimize-linear',
                  ' --arrays-reduce-sharing', ' --arrays-weak-equiv']

    elif theory == "bv":
        unique = [' --bitwise-eq', ' --bv-assert-input', ' --bv-extract-arith', ' --bv-gauss-elim', ' --bv-intro-pow2',
                  ' --bv-print-consts-as-indexed-symbols', ' --bv-propagate', ' --bv-rw-extend-eq', ' --bv-to-bool']
        regular += [" --bitblast=eager ", ' --bitwise-eq', " --bv-to-bool", " --cegqi-bv", " --cegqi-bv-ineq=eq-slack"]
    elif theory == "datatype":
        unique = [' --cdt-bisimilar', ' --dt-binary-split', ' --dt-blast-splits', ' --dt-cyclic',
                  ' --dt-force-assignment',
                  ' --dt-infer-as-lemmas', ' --dt-nested-rec', ' --dt-polite-optimize', ' --dt-rewrite-error-sel',
                  ' --dt-share-sel', ' --sygus-fair-max', ' --sygus-sym-break', ' --sygus-sym-break-agg',
                  ' --sygus-sym-break-dynamic', ' --sygus-sym-break-lazy', ' --sygus-sym-break-pbe',
                  ' --sygus-sym-break-rlv']
    elif theory == "decision":
        unique = [' --decision-use-weight', ' --jh-rlv-order']
    elif theory == "fp":
        unique = [' --fp-lazy-wb']
    elif theory == "string":
        unique = [' --re-elim', ' --re-elim-agg', ' --strings-check-entail-len', ' --strings-deq-ext',
                  ' --strings-eager',
                  ' --strings-eager-eval', ' --strings-eager-len', ' --strings-eager-len-re', ' --strings-eager-solver',
                  ' --strings-exp', ' --strings-ff', ' --strings-fmf', ' --strings-infer-as-lemmas',
                  ' --strings-infer-sym', ' --strings-lazy-pp', ' --strings-len-norm', ' --strings-mbr',
                  ' --strings-min-prefix-explain', ' --strings-regexp-inclusion', ' --strings-rexplain-lemmas',
                  ' --strings-unified-vspt']
    # return common + unique
    if mode == "regular":
        return regular
    else:
        return common + unique
    
def z3_candidate_option(theory, mode):
    new_core = [" tactic.default_tactic=smt sat.euf=true "]
    regular_opt = [" rewriter.cache_all=true ", " rewriter.eq2ineq=true ",
                   " rewriter.hoist_mul=true ", " rewriter.pull_cheap_ite=true ",
                   " rewriter.expand_nested_stores=true ",
                   " fp.xform.inline_eager=false ", " fp.xform.inline_linear_branch=true ", "rewriter.sort_sums=true",
                   " rewriter.arith_lhs=true ", " smt.bv.size_reduce=true "]
    if theory not in ["fp", "string"]:
        regular_opt += [" tactic.default_tactic=smt sat.euf=true ", " tactic.default_tactic=smt sat.euf=true ",
                        " tactic.default_tactic=smt sat.euf=true "]
    common_opt = [' pi.block_loop_patterns=false', ' pi.pull_quantifiers=false', ' pi.use_database=true',
                  ' pi.warnings=true', ' tactic.solve_eqs.context_solve=false', ' tactic.solve_eqs.ite_solver=false',
                  ' tactic.solve_eqs.theory_solver=false', ' pp.bounded=true', ' pp.bv_literals=false',
                  ' pp.bv_neg=true', ' pp.decimal=true', ' pp.fixed_indent=true', ' pp.flat_assoc=false',
                  ' pp.fp_real_literals=true', ' pp.pretty_proof=true', ' pp.simplify_implies=false',
                  ' pp.single_line=true', ' sat.abce=true', ' sat.acce=true', ' sat.anf=true', ' sat.anf.exlin=true',
                  ' sat.asymm_branch=false', ' sat.asymm_branch.all=true', ' sat.asymm_branch.sampled=false',
                  ' sat.ate=false', ' sat.bca=true', ' sat.bce=true', ' sat.binspr=true',
                  ' sat.branching.anti_exploration=true', ' sat.cardinality.solver=false', ' sat.cce=true',
                  ' sat.core.minimize=true', ' sat.core.minimize_partial=true', ' sat.cut=true', ' sat.cut.aig=true',
                  ' sat.cut.dont_cares=false', ' sat.cut.force=true', ' sat.cut.lut=true', ' sat.cut.npn3=true',
                  ' sat.cut.redundancies=false', ' sat.cut.xor=true', ' sat.dimacs.core=true',
                  ' sat.drat.activity=true', ' sat.drat.binary=true', ' sat.drat.check_sat=true',
                  ' sat.drat.check_unsat=true', ' sat.dyn_sub_res=false', ' sat.elim_vars=false',
                  ' sat.elim_vars_bdd=false', ' sat.enable_pre_simplify=true', ' sat.euf=true',
                  ' sat.force_cleanup=true', ' sat.gc.burst=true', ' sat.gc.defrag=false', ' sat.local_search=true',
                  ' sat.local_search_dbg_flips=true', ' sat.lookahead.double=false',
                  ' sat.lookahead.global_autarky=true', ' sat.lookahead.preselect=true',
                  ' sat.lookahead.use_learned=true', ' sat.lookahead_scores=true', ' sat.lookahead_simplify=true',
                  ' sat.lookahead_simplify.bca=false', ' sat.minimize_lemmas=false', ' sat.override_incremental=true',
                  ' sat.phase.sticky=false', ' sat.prob_search=true', ' sat.probing=false', ' sat.probing_binary=false',
                  ' sat.probing_cache=false', ' sat.propagate.prefetch=false', ' sat.restart.fast=false',
                  ' sat.retain_blocked_clauses=false', ' sat.scc=false', ' sat.scc.tr=false', ' sat.subsumption=false',
                  ' model.compact=false', ' model.completion=true', ' model.inline_def=true', ' model.partial=true',
                  ' model.v1=true', ' model.v2=true', ' opt.dump_benchmarks=true', ' opt.dump_models=true',
                  ' opt.elim_01=false', ' opt.enable_lns=true', ' opt.enable_sat=false', ' opt.enable_sls=true',
                  ' opt.maxlex.enable=false', ' opt.maxres.add_upper_bound_block=true', ' opt.maxres.hill_climb=false',
                  ' opt.maxres.maximize_assignment=true', ' opt.maxres.pivot_on_correction_set=false',
                  ' opt.maxres.wmax=true', ' opt.pb.compile_equality=true', ' opt.pp.neat=false', ' opt.pp.wcnf=true',
                  ' parallel.enable=true', ' nnf.ignore_labels=true', ' nnf.sk_hack=true',
                  ' model_evaluator.array_as_stores=false', ' model_evaluator.array_equalities=false',
                  ' model_evaluator.completion=true', ' rewriter.algebraic_number_evaluator=false',
                  ' rewriter.arith_ineq_lhs=true', ' rewriter.arith_lhs=true', ' rewriter.bit2bool=false',
                  ' rewriter.blast_distinct=true', ' rewriter.blast_eq_value=true', ' rewriter.blast_select_store=true',
                  ' rewriter.bv_extract_prop=true', ' rewriter.bv_ite2id=true', ' rewriter.bv_le_extra=true',
                  ' rewriter.bv_not_simpl=true', ' rewriter.bv_sort_ac=true', ' rewriter.cache_all=true',
                  ' rewriter.coalesce_chars=false', ' rewriter.elim_and=true', ' rewriter.elim_ite=false',
                  ' rewriter.elim_rem=true', ' rewriter.elim_sign_ext=false', ' rewriter.elim_to_real=true',
                  ' rewriter.eq2ineq=true', ' rewriter.expand_nested_stores=true', ' rewriter.expand_power=true',
                  ' rewriter.expand_select_ite=true', ' rewriter.expand_select_store=true',
                  ' rewriter.expand_store_eq=true', ' rewriter.expand_tan=true', ' rewriter.flat=false',
                  ' rewriter.gcd_rounding=true', ' rewriter.hi_div0=false', ' rewriter.hi_fp_unspecified=true',
                  ' rewriter.hoist_ite=true', ' rewriter.hoist_mul=true',
                  ' rewriter.ignore_patterns_on_ground_qbody=false', ' rewriter.ite_extra_rules=true',
                  ' rewriter.local_ctx=true', ' rewriter.mul2concat=true', ' rewriter.mul_to_power=true',
                  ' rewriter.pull_cheap_ite=true', ' rewriter.push_ite_arith=true', ' rewriter.push_ite_bv=true',
                  ' rewriter.push_to_real=false', ' rewriter.rewrite_patterns=true', ' rewriter.som=true',
                  ' rewriter.sort_store=true', ' rewriter.sort_sums=true', ' rewriter.split_concat_eq=true',
                  ' smt.arith.auto_config_simplex=true', ' smt.arith.bprop_on_pivoted_rows=false',
                  ' smt.arith.eager_eq_axioms=false', ' smt.arith.enable_hnf=false',
                  ' smt.arith.greatest_error_pivot=true', ' smt.arith.ignore_int=true', ' smt.arith.int_eq_branch=true',
                  ' smt.arith.min=true', ' smt.arith.nl=false', ' smt.arith.nl.branching=false',
                  ' smt.arith.nl.expp=true', ' smt.arith.nl.grobner=false', ' smt.arith.nl.horner=false',
                  ' smt.arith.nl.nra=false', ' smt.arith.nl.order=false', ' smt.arith.nl.tangents=false',
                  ' smt.arith.print_ext_var_names=true', ' smt.arith.print_stats=true',
                  ' smt.arith.propagate_eqs=false', ' smt.arith.random_initial_value=true',
                  ' smt.array.extensional=false', ' smt.array.weak=true', ' smt.auto_config=false',
                  ' smt.bv.delay=false', ' smt.bv.enable_int2bv=false', ' smt.bv.eq_axioms=false',
                  ' smt.bv.reflect=false', ' smt.bv.watch_diseq=true', ' smt.candidate_models=true',
                  ' smt.clause_proof=true', ' smt.core.extend_nonlocal_patterns=true', ' smt.core.extend_patterns=true',
                  ' smt.core.minimize=true', ' smt.dack.eq=true', ' smt.delay_units=true',
                  ' smt.ematching=false', ' smt.induction=true', ' smt.macro_finder=true', ' smt.mbqi=false',
                  ' smt.mbqi.trace=true', ' smt.pb.learn_complements=false', ' smt.pull_nested_quantifiers=true',
                  ' smt.qi.profile=true', ' smt.quasi_macros=true', ' smt.refine_inj_axioms=false',
                  ' smt.restricted_quasi_macros=true', ' smt.seq.split_w_len=false', ' smt.seq.validate=true',
                  ' smt.str.aggressive_length_testing=true', ' smt.str.aggressive_unroll_testing=false',
                  ' smt.str.aggressive_value_testing=true', ' smt.str.fast_length_tester_cache=true',
                  ' smt.str.fast_value_tester_cache=false', ' smt.str.fixed_length_naive_cex=false',
                  ' smt.str.fixed_length_refinement=true', ' smt.str.string_constant_cache=false',
                  ' smt.str.strong_arrangements=false', ' smt.theory_aware_branching=true',
                  ' smt.theory_case_split=true']

    if theory in ["real", "int"]:
        common_opt = common_opt + [' nlsat.check_lemmas=true', ' nlsat.factor=false', ' nlsat.inline_vars=true',
                                   ' nlsat.minimize_conflicts=true', ' nlsat.randomize=false',
                                   ' nlsat.reorder=false', ' nlsat.shuffle_vars=true',
                                   ' nlsat.simplify_conflicts=false']
    if theory not in ["fp", "string"]:
        common_opt = common_opt + new_core
    if mode == "regular":
        return regular_opt
    else:
        return common_opt
    

def bitwuzla_candidate_option():
    options = [
        "--bv-solver preprop",
        "--bv-solver prop",
        "--bv-solver bitblast",
        "-rwl 2",
        "-rwl 3",
        "-rwl 1",
        "-rwl 0",
        "-rwl 4",
        "--sat-solver kissat",
        "--sat-solver cms",
        "--sat-solver cadical",
        "--no-prop-const-bits",
        "--no-prop-ineq-bounds",
        "--prop-nprops 1",
        "--prop-nprops 2",
        "--prop-nprops 3",
        "--prop-nupdates 1",
        "--prop-nupdates 2",
        "--prop-nupdates 3",
        "--prop-opt-lt-concat-sext",
        "--prop-path-sel random",
        "--prop-path-sel essential",
        "--no-prop-sext",
        "--prop-normalize",
        "--no-preprocess",
        "--pp-contr-ands",
        "--pp-elim-extracts",
        "--no-pp-embedded",
        "--no-pp-flatten-and",
        "--no-pp-normalize",
        "--no-pp-normalize-share-aware",
        "--no-pp-skeleton-preproc",
        "--no-pp-variable-subst",
        "--no-pp-variable-subst-norm-eq",
        "--pp-variable-subst-norm-diseq",
        "--pp-variable-subst-norm-bv-ineq"
        ]
    return options

z3_options = z3_candidate_option("all", "regular")
cvc5_options = cvc5_candidate_option("all", "regular")
bitwuzla_options = bitwuzla_candidate_option()