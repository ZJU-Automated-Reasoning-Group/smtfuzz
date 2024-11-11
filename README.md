## smtfuzz: A random generator for SMT-LIB2 formulas



SMT solvers are automated tools that can determine the satisfiability of logical formulas in various theories, including arithmetic, bit-vectors, arrays, and more.
smtfuzz is a random generator for SMT-LIB2 formulas. It is designed to help users generate test cases for SMT solvers and explore various SMT-LIB2 features.

## Installation

To install a stable version of smtfuzz:
~~~~
pip3 install smtfuzz
~~~~

## Usage
After installing the package, you can type
~~~~
`smtfuzz`
~~~~~
And you will see an SMT-LIB2 formula on the screen.

For more advanced options, please use the `-h` flag to display the help menu.
Feel free to experiment with different combinations of options to generate a wide variety of SMT-LIB2 formulas for testing purposes.

## Feedback

Please submit an issue to report any bugs, issues, questions, or feature requests. We are pleased to receive your 
feedback.


## Citing SMTFuzz
You are kindly asked to acknowledge usage of the tool by citing the following paper

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
