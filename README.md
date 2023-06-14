## smtfuzz: A random generator for SMT-LIB2 formulas



SMT solvers are automated tools that can decide the satisfiability of logical formulas in a variety of theories, including arithmetic, bit-vectors, arrays, and more.
smtfuzz is a random generator for SMT-LIB2 formulas. It is designed to help users generate test cases for SMT solvers and explore various SMT-LIB2 features.

## Installation

To install a stable version of smtfuzz:
~~~~
pip3 install smtfuzz
~~~~

## Usage
After installing the package, you can just type
~~~~
`smtfuzz`
~~~~~
and you will see an SMT-LIB2 formula in the screen.

For more advanced options, please use the `-h` flag to display the help menu.
Feel free to experiment with different combinations of options to generate a wide variety of SMT-LIB2 formulas for testing purposes.

## Feedback

To report any bugs, issues, questions or feature requests, 
please submit an issue. We are pleased to receive your 
feedback.


## Citing SMTFuzz
You are kindly asked to acknowledge usage of the tool by citing the 
following papers
~~~~
@inproceedings{DBLP:conf/sigsoft/YaoHTSWZ21,
  author       = {Peisen Yao and
                  Heqing Huang and
                  Wensheng Tang and
                  Qingkai Shi and
                  Rongxin Wu and
                  Charles Zhang},
  title        = {Skeletal approximation enumeration for SMT solver testing},
  booktitle    = {ESEC/FSE'21: 29th ACM Joint European Software Engineering Conference
                  and Symposium on the Foundations of Software Engineering, Athens,
                  Greece, August 23-28, 2021},
  pages        = {1141--1153},
  publisher    = {ACM},
  year         = {2021},
  doi          = {10.1145/3468264.3468540}
}
~~~~

~~~~
@inproceedings{DBLP:conf/issta/YaoHTSWZ21,
  author       = {Peisen Yao and
                  Heqing Huang and
                  Wensheng Tang and
                  Qingkai Shi and
                  Rongxin Wu and
                  Charles Zhang},
  title        = {Fuzzing SMT solvers via two-dimensional input space exploration},
  booktitle    = {ISSTA'21: 30th ACM SIGSOFT International Symposium on Software
                  Testing and Analysis, Virtual Event, Denmark, July 11-17, 2021},
  pages        = {322--335},
  publisher    = {ACM},
  year         = {2021},
  doi          = {10.1145/3460319.3464803}
}
~~~~
