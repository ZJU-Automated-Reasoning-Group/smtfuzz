## smtfuzz: A random generator for SMT-LIB2 formulas



SMT solvers are automated tools that can determine the satisfiability of logical formulas in various theories, including arithmetic, bit-vectors, arrays, and more.
smtfuzz is a random generator for SMT-LIB2 formulas. It is designed to help users generate test cases for SMT solvers and explore various SMT-LIB2 features.

## Installation

To install a stable version of smtfuzz:
~~~~
pip3 install smtfuzz
~~~~

Install from source
~~~~
pip install -e .
~~~~

## Usage

After installing the package, you can type
~~~~
smtfuzz
~~~~
And you will see an SMT-LIB2 formula on the screen.

For more advanced options, please use the `-h` flag to display the help menu. Feel free to experiment with different combinations of options to generate a wide variety of SMT-LIB2 formulas for testing purposes.

## Feedback

Please submit an issue to report any bugs, issues, questions, or feature requests. We are pleased to receive your 
feedback.


## Detected Bugs

https://smtfuzz.github.io/

## Publications

~~~~
@inproceedings{fse21skeletal,
  title={Skeletal Approximation Enumeration for SMT Solver Testing},
  author={Yao, Peisen and Huang, Heqing and Tang, Wensheng and Shi, Qingkai and Wu, Rongxin and Zhang, Charles},
  booktitle={Proceedings of the ACM Joint European Software Engineering Conference and Symposium on the Foundations of Software Engineering},
  series={ESEC/FSE 2021},
  year={2021},
  publisher={ACM}
}

@inproceedings{issta21opt,
  title={Fuzzing SMT Solvers via Two-Dimensional Input Space Exploration},
  author={Yao, Peisen and Huang, Heqing and Tang, Wensheng and Shi, Qingkai and Wu, Rongxin and Zhang, Charles},
  booktitle={Proceedings of the 30th ACM SIGSOFT International Symposium on Software Testing and Analysis},
  series={ISSTA 2021},
  year={2021},
  publisher={ACM}
}
~~~~
