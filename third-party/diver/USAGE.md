
## How to Use Diver
You can use Diver to test an SMT Solver as follows (the instructions can be also found via ```python3 __main__.py --help```):
```bash
$ python3 __main__.py -i <SEED_DIR> -s <SOLVER> -b <SOLVER_PATH> -o <SOLVER_OPTION> -t <SOLVER_TIME> -l <LOGIC> -m <MUTANTS_NUMBER>
```

* ``-i`` : can be the directory that contains seed formulas, or can be the path of a single seed formula (.smt2 file). Seed formulas can be downloaded from [SMT-LIB website](http://smtlib.cs.uiowa.edu/benchmarks.shtml).
* ``-s`` : name of an SMT Solver to test (e.g., z3, cvc, dreal).
* ``-b`` : path of the binary of an SMT Solver to test (e.g., ../z3/build/z3, ../cvc5/build/bin/cvc5).
* ``-o`` : options that will be used to invoke an SMT Solver. Multiple options can be provided using comma (e.g., ``smt.string_solver=z3str3,rewriter.flat=false``).
* ``-t`` : SMT Solver timeout (in seconds, default: 10).
* ``-l`` : logic of an input seed formula (e.g., QF_SLIA, QF_NRA, ...).
* ``-m`` : number of statisfiable mutants that will be generated from a given input seed formula (default : 1,000).

## Running Example
* Suppose the directory ``../benchmark`` contains seed formulas in ``QF_SLIA`` logic.
To test CVC5 (where the binary is located at ``/solvers/cvc5-1.0.1/build/bin/cvc5``) using Diver, run the following command:
```bash
$ timeout 1800 python3 __main__.py -i ../benchmark -s cvc -b /solvers/cvc5-1.0.1/build/bin/cvc5 -l QF_SLIA
```

* If Diver found bugs, the directory ```./bug_dir``` will be generated. ```./bug_dir``` will have subdirectories tagged with names of bug types. For example, if you found bugs in CVC5 SMT solver, ```./bug_dir``` will have the following structure:
```text
bug_dir
├── cvc_soundness: the directory for refutational soundness bugs detected in CVC5.
│            ├── <SEED1>
│            |      ├── <SEED1>.smt2
│            |      └── <BUG_TRIGGERING_MUTANT>.smt2     
│            ├── <SEED2>         
│            |      ├── <SEED2>.smt2
│            │      ...                     
│            ...   
├── cvc_invalid: the directory for invalid-model bugs detected in CVC5.
│            ├── <SEED3>
|            ...  
└── cvc_crash: the directory for crash bugs detected in CVC5.
        ...
```
