# Diver
Diver is a black-box fuzzer for SMT Solvers. The technical details of Diver can be found in our paper accepted to ICSE 2023: "Diver: Oracle-Guided SMT Solver Testing with Unrestricted Random Mutations"

## Installation

* Install Python libraries below:
```bash
pip3 install pyinterval pyparsing toml rstr termcolor numpy z3-solver cvc5
```

* Install Z3:
```bash
wget https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.11.0.tar.gz
tar -xvzf z3-4.11.0.tar.gz
cd z3-z3-4.11.0
python3 scripts/mk_make.py --python
cd build
make -j 4
sudo make install
```

* Install CVC5:
```bash
wget https://github.com/cvc5/cvc5/archive/refs/tags/cvc5-1.0.1.tar.gz
tar -xvzf cvc5-1.0.1.tar.gz
cd cvc5-cvc5-1.0.1
./configure.sh --auto-download
cd build
make -j 4 
sudo make install
```

## Usage
Please see [USAGE.md](./USAGE.md).

## Structure of Diver
Please see [STRUCTURE.md](https://github.com/kupl/Diver/blob/main/STRUCTURE.md) for implementation of Diver.

## Research Artifact for ICSE 2023 paper
To reproduce the experimental results in our ICSE 2023 paper, please visit: https://github.com/kupl/Diver-Artifact
