"""
MIT License

Copyright (c) 2023 The histfuzz authors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""

import subprocess
import os
import random

from src.utils.file_operation import record_bug, get_smt_files_list


def solver_runner(solver1_path, solver2_path, smt_file, timeout, incremental, solver1, solver2,
                  theory, add_option, temp, tactic=None):
    # Prepare temporary file names
    temp_file_name1 = smt_file
    temp_file_name1 = temp_file_name1.replace(".smt2", "")
    temp_file_name2 = temp_file_name1 + "_output2.txt"
    temp_file_name1 += "_output1.txt"
    temp_file_path1 = temp_file_name1
    temp_file_path2 = temp_file_name2
    # Prepare SMT file names
    smt_file1 = smt_file
    smt_file2 = smt_file
    # If tactic is None, randomly add check-sat-using to the test instance for a Z3 solver
    if tactic is None and add_option != "default":
        add_check_sat_using_flag = random.choice([False, True])
        if add_check_sat_using_flag and solver1 == "z3":
            tactic = z3_tactic(smt_file1)
            smt_file1 = tactic.add_check_sat_using()
        if add_check_sat_using_flag and solver2 == "z3":
            tactic = z3_tactic(smt_file2)
            smt_file2 = tactic.add_check_sat_using()
    else:
        # Otherwise, add the specific tactic to the SMT file of the corresponding solver
        if solver1 == "z3":
            smt_file1 = add_specific_tactic(smt_file1, tactic)
        if solver2 == "z3":
            smt_file2 = add_specific_tactic(smt_file2, tactic)
    # Prepare solver option notes and commands
    solver1_opt_note, solver2_opt_note = "", ""
    z3_opt, cvc5_option = add_option_to_command(theory, add_option)
    # Add solver options to the option notes of the corresponding solver
    if z3_opt is not None and solver1 == "z3":
        solver1_opt_note += z3_opt + "\n"
    if cvc5_option is not None and solver1 == "cvc5":
        solver2_option_note += cvc5_option + "\n"
    # Prepare the command for the first solver
    command1 = command_line(solver1_path, solver1, smt_file1, timeout, incremental, temp_file_path1, z3_option=z3_opt,
                            cvc5_opt=cvc5_option)
    z3_opt, cvc5_option = add_option_to_command(theory, add_option)
    # Add solver options to the option notes of the corresponding solver
    if z3_opt is not None and solver2 == "z3":
        solver2_opt_note = z3_opt
    if cvc5_option is not None and solver2 == "cvc5":
        solver2_opt_note = cvc5_option
    # Prepare the command for the second solver
    command2 = command_line(solver2_path, solver2, smt_file2, timeout, incremental, temp_file_path2, z3_option=z3_opt,
                            cvc5_opt=cvc5_option)
    # Run the solvers and get their outputs
    solver_output1, error_msg1 = creat_process_and_get_result(command1, temp_file_path1, incremental)
    solver_output2, error_msg2 = creat_process_and_get_result(command2, temp_file_path2, incremental)
    # Check the solvers' outputs
    soundness, invalid_model, crash = check_result(solver_output1, solver_output2, solver1, solver2, smt_file1,
                                                   smt_file2, incremental, temp, error_msg1, error_msg2,
                                                   solver1_opt_note, solver2_opt_note)
    if soundness or invalid_model or crash:
        return True
    else:
        return False


def read_result(file_path, incremental):
    try:
        with open(file_path, 'r') as f:
            lines = f.read().splitlines()
            # print(lines)
    except:
        # print(colored("CANT OPEN THE FILE", "red", attrs=["bold"]))
        return "error"

    for line in lines:

        if line.find("Parse Error") != -1:
            os.remove(file_path)
            return "parseerror"

        if line.find("Segmentation fault") != -1:
            os.remove(file_path)
            return "segfault"

        # java.lang.NullPointerException
        if line.find("NullPointerException") != -1:
            os.remove(file_path)
            return "nullpointer"

        if line.find("invalid model") != -1 or line.find("ERRORS SATISFYING") != -1:
            os.remove(file_path)
            return "invalid model"

        if line.find("ASSERTION VIOLATION") != -1:
            os.remove(file_path)
            return "assertviolation"

        # java.lang.AssertionError
        if line.find("AssertionError") != -1:
            os.remove(file_path)
            return "assertviolation"

        if line.find("option parsing") != -1:
            os.remove(file_path)
            return "option error"

        if line.find("approximate values") != -1:
            os.remove(file_path)
            return "approximation"

        if line.find("failure") != -1:
            os.remove(file_path)
            return "failure"

        if line.find("error") != -1 or line.find("unsupported reserved word") != -1:
            os.remove(file_path)
            return "error"

    # Incremental mode
    if incremental == "incremental":

        result_list = []
        for line in lines:
            result_list.append(line)
        os.remove(file_path)
        if result_list:
            return result_list
        else:
            return "timeout"
    else:

        if len(lines) > 0:
            if lines[0] == "sat" or lines[0] == "unsat" or lines[0] == "unknown":
                os.remove(file_path)
                return lines[0]
            else:
                os.remove(file_path)
                return "error"
        else:
            os.remove(file_path)
            return "timeout"


def check_result(result1, result2, solver1, solver2, bug_file1_path, bug_file2_path,
                 incremental, temp, message1, message2, solver1_opt=None, solver2_opt=None):
    crash_flag = False
    soundness_flag = False
    invalid_model_flag = False
    opt = ""
    if solver1_opt is not None:
        opt += "solver1-" + solver1 + ": "
        if solver1 == "z3":
            opt += "model_validate=true " + solver1_opt
        elif solver1 == "cvc5":
            opt += "-i --strings-exp --check-models " + solver1_opt
    if solver2_opt is not None:
        opt += "solver2-" + solver2 + ": "
        if solver2 == "z3":
            opt += "model_validate=true " + solver2_opt
        elif solver2 == "cvc5":
            opt += "-i --strings-exp --check-models " + solver2_opt
    # print("result1: ", result1, "\nresult2: ", result2)
    if result1 in ["timeout", "error", "parseerror", "option error"] and result2 in ["timeout", "error", "parseerror",
                                                                                     "option error"]:
        pass
    if result1 in ["nullpointer", "assertviolation", "segfault", "fatalfailure", "address error", "crash"]:
        record_bug(temp, "crash", bug_file1_path, bug_file2_path, solver1, result1, "", "", option=opt)
        crash_flag = True
    if result2 in ["nullpointer", "assertviolation", "segfault", "fatalfailure", "address error", "crash"]:
        record_bug(temp, "crash", bug_file1_path, bug_file2_path, "", "", solver2, result2, option=opt)
        crash_flag = True
    if result1 == "invalid model":
        record_bug(temp, "InvalidModel", bug_file1_path, bug_file2_path, solver1, result1, "", "",
                   option=opt)
        invalid_model_flag = True
    if result2 == "invalid model":
        record_bug(temp, "InvalidModel", bug_file1_path, bug_file2_path, "", "", solver2, result2,
                   option=opt)
        invalid_model_flag = True
    if (result1 in ["sat", "unsat"] and result2 in ["sat", "unsat"]) or (
            isinstance(result1, list) and isinstance(result2, list)):
        if solver1 == solver2 or check_special(bug_file1_path):
            if isinstance(result1, list) and isinstance(result2, list):
                result_count = len(result1)
                if result_count > len(result2):
                    result_count = len(result2)
                for idx in range(result_count):
                    if result1[idx] != result2[idx] and result1[idx] in ["sat", "unsat"] and result2[idx] in ["sat",
                                                                                                              "unsat"]:
                        record_bug(temp, "soundness", bug_file1_path, bug_file2_path, solver1, result1, solver2,
                                   result2, opt)
                        soundness_flag = True
                        break
            elif result1 != result2 and result1 in ["sat", "unsat"] and result2 in ["sat", "unsat"]:
                record_bug(temp, "soundness", bug_file1_path, bug_file2_path, solver1, result1, solver2, result2, opt)
                soundness_flag = True
    return soundness_flag, invalid_model_flag, crash_flag


def command_line(solver_path, solver, smt_file, timeout, incremental, output_path, check_bug_type="model",
                 z3_option=None, cvc5_opt=None):
    command = "timeout " + str(timeout) + "s "
    if solver in ["yices2", "boolector", "bitwuzla"] and incremental == "incremental":
        command += solver_path + " --incremental "
    elif solver == "cvc5":
        command += solver_path + " -q --strings-exp "
        if incremental == "incremental":
            command += " -i "
    else:
        command += solver_path
    if solver == "yices2":
        if random.choice([True, False]):
            command += " --mcsat "
    if check_bug_type == "model":
        if solver == "z3":
            # command += " tactic.default_tactic=smt sat.euf=true model_validate=true"
            command += " model_validate=true "
        elif solver == "cvc5":
            command += " --check-models "
        elif solver == "bitwuzla":
            command += " --check-model "
    if z3_option is not None and solver == "z3":
        command += " " + z3_option
    if cvc5_opt is not None and solver == "cvc5":
        command += " " + cvc5_opt
    command += " " + smt_file + " > " + output_path
    return command


class z3_tactic:
    def __init__(self, exported_file_path):
        self.tactic_list = ["sat", "smt", "ctx-solver-simplify", "unit-subsume-simplify", "aig", "purify-arith", "fm",
                            "blast-term-ite", "ctx-simplify", "der", "elim-term-ite", "elim-uncnstr", "pb-preprocess",
                            "reduce-args", "nlsat", "nlqsat", "qe-light", "qe", "qsat", "qe2",
                            "simplify", "elim-and", "symmetry-reduce", "default", "cofactor-term-ite",
                            "special-relations", "fix-dl-var", "factor", "distribute-forall",
                            "solve-eqs", "dom-simplify", "sat-preprocess", "degree-shift", "injectivity", "snf", "nnf",
                            "occf", "sat-preprocess", "subpaving", "bit-blast", "propagate-values",
                            "reduce-invertible", "split-clause"]
        self.file = exported_file_path

    def _random_construct_tactic(self):
        tactic_count = random.randint(1, 3)
        tactics = ""
        if tactic_count == 1:
            tactics += random.choice(self.tactic_list)
        else:
            tactics += "(then"
            for i in range(tactic_count):
                tactics += " " + random.choice(self.tactic_list)
            tactics += ")"
        return tactics

    def add_check_sat_using(self):
        """
            Replace the normal (check-sat) with (check-sat-using)
        """
        check_sat_using_option = self._random_construct_tactic()

        try:
            with open(self.file, 'r') as f:
                lines = f.read().splitlines()
        except:
            print("#######" + "ERROR OCCURRED IN 'check_sat_using'")
        for i in range(len(lines)):
            if lines[i].find("(check-sat)") != -1:
                lines[i] = "(check-sat-using " + check_sat_using_option + ")" + "\n"
            else:
                lines[i] = lines[i] + "\n"
        new_file = self.file.replace(".smt2", "_tactic.smt2")
        file = open(new_file, "w")
        file.writelines(lines)
        file.close()
        return new_file


def add_specific_tactic(file_path, tactics):
    try:
        with open(file_path, 'r') as f:
            lines = f.read().splitlines()
    except:
        print("#######" + "ERROR OCCURRED IN 'check_sat_using'")
    for i in range(len(lines)):
        if lines[i].find("(check-sat)") != -1:
            lines[i] = "(check-sat-using " + tactics + ")" + "\n"
        else:
            lines[i] = lines[i] + "\n"
    new_file = file_path.replace(".smt2", "_tactic.smt2")
    file = open(new_file, "w")
    file.writelines(lines)
    file.close()
    return new_file


def cvc5_candidate_option(theory, mode):
    common = [' --abstract-values', ' --ackermann', ' --early-ite-removal', ' --expand-definitions',
              ' --ext-rew-prep=use',
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
               '--check-interpolants', '--check-proofs', '--check-synth-sol', '--check-unsat-cores',
               '--decision=justification',
               '--decision=stoponly', '--enum-inst', '--enum-inst-interleave', '--enum-inst-sum', '--ext-rew-prep=agg',
               '--ext-rew-prep=use', '--ext-rewrite-quant', '--finite-model-find', '--fmf-bound', '--fmf-fun',
               '--fmf-fun-rlv',
               '--full-saturate-quant', '--ho-elim', '--inst-when=full', '--inst-when=full-delay',
               '--inst-when=full-delay-last-call',
               '--inst-when=last-call', '--interpolants-mode=default', '--interpolants-mode=assumptions',
               '--interpolants-mode=conjecture',
               '--interpolants-mode=shared', '--interpolants-mode=all', '--cegqi-bv-ineq=eq-slack', '--check-abducts',
               '--ite-lift-quant=all', '--ite-lift-quant=none', '--learned-rewrite', '--macros-quant',
               '--macros-quant-mode=all',
               '--macros-quant-mode=ground', '--mbqi-one-inst-per-round', '--miniscope-quant=off',
               '--miniscope-quant=conj',
               '--miniscope-quant=fv', '--miniscope-quant=agg', '--multi-trigger-cache', '--multi-trigger-priority',
               '--nl-ext-tplanes-interleave', '--nl-ext=none', '--nl-ext=light', '--no-arith-brab', '--nl-cov',
               '--no-arrays-eager-index', '--no-bitwise-eq', '--no-cbqi', '--no-cegqi-bv', '--no-cegqi-innermost',
               '--no-dt-share-sel', '--no-e-matching', '--no-elim-taut-quant', '--no-ho-elim-store-ax',
               '--no-inst-no-entail',
               '--no-multi-trigger-linear', '--no-nl-ext-factor', '--no-nl-ext-rewrite', '--no-nl-ext-tf-tplanes',
               '--no-nl-ext-tplanes', '--no-print-inst-full', '--no-produce-assertions', '--no-quant-alpha-equiv',
               '--no-static-learning', '--no-strings-check-entail-len', '--no-strings-eager-eval',
               '--no-strings-eager-solver',
               '--no-strings-lazy-pp', '--no-strings-mbr', '--no-strings-regexp-inclusion',
               '--no-sygus-add-const-grammar',
               '--no-sygus-min-grammar', '--no-sygus-pbe', '--no-sygus-sym-break-pbe', '--no-uf-ss-fair',
               '--no-var-elim-quant',
               '--no-var-ineq-elim-quant', '--pre-skolem-quant=agg', '--pre-skolem-quant=on', '--prenex-quant-user',
               '--prenex-quant=none', '--print-unsat-cores-full', '--produce-abducts', '--produce-assignments',
               '--produce-difficulty',
               '--produce-interpolants', '--produce-learned-literals', '--produce-proofs',
               '--produce-unsat-assumptions',
               '--produce-unsat-cores', '--quant-dsplit=agg', '--quant-dsplit=none', '--re-elim=agg', '--re-elim=on',
               '--multi-trigger-when-single', '--relevant-triggers', '--sets-ext', '--solve-real-as-int',
               '--simplification=none',
               '--sort-inference', '--static-learning', '--strings-deq-ext', '--strings-eager-len-re', '--strings-exp',
               '--strings-fmf', '--strings-process-loop-mode=none', '--sygus', '--sygus-core-connective',
               '--sygus-enum=random', '--sygus-enum=smart', '--sygus-enum=fast', '--sygus-enum=var-agnostic',
               '--sygus-eval-unfold=none', '--sygus-eval-unfold=single', '--sygus-eval-unfold=multi',
               '--sygus-fair=none',
               '--sygus-fair=direct', '--sygus-fair=dt-height-bound', '--sygus-fair=dt-size-bound',
               '--prenex-quant=norm',
               '--sygus-grammar-cons=any-term-concise', '--sygus-grammar-cons=any-const',
               '--sygus-grammar-cons=any-term',
               '--sygus-inst', '--sygus-inv-templ=none', '--sygus-inv-templ=pre', '--sygus-out=status',
               '--sygus-out=status-and-def', '--sygus-repair-const', '--sygus-rewriter=none', '--sygus-rewriter=basic',
               '--sygus-si-abort', '--sygus-si-rcons=none', '--sygus-si-rcons=try', '--sygus-si-rcons=all-limit',
               '--sygus-si=all', '--sygus-si=use', '--sygus-simple-sym-break=none', '--sygus-simple-sym-break=basic',
               '--sygus-stream', '--sygus-unif-pi=cond-enum-igain', '--sygus-unif-pi=complete',
               '--sygus-unif-pi=cond-enum',
               '--term-db-mode=relevant', '--trigger-sel=all', '--trigger-sel=max', '--trigger-sel=min-s-max',
               '--trigger-sel=min-s-all',
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
                   " smt.bv.eq_axioms=false ", " rewriter.expand_nested_stores=true ",
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


def add_option_to_command(theory, add_flag):
    if add_flag == "default":
        return None, None
    else:
        opt_count = random.choice([0, 1, 2])
        if opt_count == 1:
            z3_opt = random.choice(z3_candidate_option(theory, add_flag))
            cvc5_option = random.choice(cvc5_candidate_option(theory, add_flag))
        elif opt_count == 2:
            z3_opt = random.choice(z3_candidate_option(theory, add_flag)) + \
                     random.choice(z3_candidate_option(theory, add_flag))
            cvc5_option = random.choice(cvc5_candidate_option(theory, add_flag))
        else:
            z3_opt = " "
            cvc5_option = " "
        return z3_opt, cvc5_option


def creat_process_and_get_result(command, temp_file, incremental):
    """
    run solver using commandline and obtain the result solver return
    :param command: command line
    :param temp_file: the output file solver gives
    :param incremental: the formula mode
    :return: the solver output
    """
    p = subprocess.Popen(command, shell=True, stderr=subprocess.PIPE)
    terminal_output = p.stderr.read().decode()
    solver_output = None
    # Process terminal output first before result parsing
    if check_crash(terminal_output) and ignore_crash(terminal_output):
        solver_output = "crash"
        if "Segmentation fault" not in terminal_output:
            err_info.append(terminal_output)
    if terminal_output.find("option parsing") != -1:
        solver_output = "option error"
    if terminal_output.find("approximate values") != -1:
        solver_output = "approximation"
    if terminal_output.find("invalid model") != -1 or terminal_output.find("ERRORS SATISFYING") != -1:
        solver_output = "invalid model"
    if terminal_output.find("Error") != -1 and solver_output is None:
        solver_output = "error"
    if solver_output is None:
        solver_output = read_result(temp_file, incremental)
    return solver_output, terminal_output


def save_valid_file_for_differential_test(solver1_path, solver2_path, solver3_path, solver1, solver2, solver3, smt_file,
                                          to):
    temp_file_name = smt_file
    temp_file_name = temp_file_name.replace(".smt2", "_output.txt")
    temp_file_path = temp_file_name
    command1 = command_line(solver1_path, solver1, smt_file, to, "no", temp_file_path)
    command2 = command_line(solver2_path, solver2, smt_file, to, "no", temp_file_path)
    command3 = command_line(solver3_path, solver3, smt_file, to, "no", temp_file_path)

    result1 = creat_process_and_get_result(command1, temp_file_path, "no")
    result2 = creat_process_and_get_result(command2, temp_file_path, "no")
    result3 = creat_process_and_get_result(command3, temp_file_path, "no")

    file_score = 0
    if result1 in ["sat", "unsat", "unknown"]:
        file_score += 1
    if result2 in ["sat", "unsat", "unknown"]:
        file_score += 1
    if result3 in ["sat", "unsat", "unknown"]:
        file_score += 1
    print(command2)
    print(command3)
    print("result1: ", result1, "result2: ", result2, "result3: ", result3)
    if file_score >= 2:
        return smt_file
    else:
        return None


def check_special(buggy_file):
    with open(buggy_file, "r") as f:
        content = f.read()
    if "^" in content:
        return False
    else:
        return True


def recheck(path):
    files = get_smt_files_list(path)
    for f in files:
        if "case" in f:
            print(f)
            solver_runner("/z3/build/z3", "/cvc5/build/bin/cvc5", f, 10, "no", "z3", "cvc5", [f])


def check_crash(output: str):
    crash_list = ["Exception", "lang.AssertionError", "lang.Error", "runtime error", "LEAKED", "Leaked",
                  "Segmentation fault", "segmentation fault", "segfault", "ASSERTION", "Assertion", "Fatal failure",
                  "Internal error detected", "an invalid model was generated", "Failed to verify", "failed to verify",
                  "ERROR: AddressSanitizer:", "invalid expression", "Aborted", "AddressSanitizer",
                  "NULL pointer was dereferenced", "ast_manager LEAKED"]
    for c in crash_list:
        if output.find(c) != -1:
            return True
    return False


def ignore_crash(output: str):
    for i in err_info:
        if output.find(i) != -1:
            return False
    return True


err_info = ["floatingpoint_literal_symfpu_traits.cpp"]
