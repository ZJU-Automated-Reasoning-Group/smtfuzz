# Implementation of Diver

We implemented Diver in Python code. The detailed structure for Diver is as follows:

```text
Diver                           <- The Diver tool directory (./Diver)
│
├── __main__.py                 <- The main implementation of Diver at the Algorthm 1 in our paper.
│
├── analyzer:                   
│         ├── pre_analyzer.py   <- The module of pre-analysis at the Algorithm 2 in our paper.
│         │                        We developed it, which generates the constraints for functions in each logic
│         ...                      such as boolean, integer, real and string, on top of the py inteval library and re module.
│         └── ...    
├── fuzzer:                    
│       ├── generator.py        <- The module for generating satisfiable mutants at the Algorithm 3 in our paper.
│       └── evaluator.py        <- The module for checking whether a mutant formula is satisfiable by model of the seed formula.
├── parser:                       
│        └── smt_parser.py      <- The module for parsing SMT-LIB2 language.
│
└── utils:                    
      ├── ...
      ...
      └── ... 
```
