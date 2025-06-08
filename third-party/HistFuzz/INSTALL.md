# **Option 1: Using Docker Image**
To get into the container, you need:

* Download the Docker Image histfuzz.tar. You can download the compressed package (about 4G) from https://doi.org/10.5281/zenodo.7631379 or https://drive.google.com/file/d/1JN8hG8qKGoQMcn8Jnmbw3iqLpWYNhT_q/view?usp=sharing.
* Generate Image data file histfuzz.tar by using command `unzip histfuzz.tar.zip`.
* docker import histfuzz.tar
* docker run -it [image id] /bin/bash


# **Option 2: Installing From Sources**

## **Step 1: Installing dependencies needed by HistFuzz**
HistFuzz needs Python library efficient-apriori, antlr, and github3.py. 

```
pip3 install efficient-apriori 
pip3 install antlr4-python3-runtime==4.9.2
pip3 install github3.py
```

## **Step 2: Installing subject solvers**

* Install dependencies following the guidance of SMT solvers, e.g., [z3](https://github.com/Z3Prover/z3) and [cvc5](https://github.com/cvc5/cvc5).
* Download source, build, and install the solvers. 
* To evaluate the code coverage of solvers achieved by testing tools, you shold enable gcov support when building solvers. 
  For example, to build z3 with gcov, you can use the command:
```
CFLAGS=--coverage CXXFLAGS=--coverage LDFLAGS=--coverage python scripts/mk_make.py
cd build; make
```
For cvc5, you should use the command:
```
./configure.sh debug --coverage --auto-download
cd build; make
```

## **Step 3: Installing the baselines of evaluation**

* Unzip the compressed files in the `histfuzz/baselines`  directory.
* Install storm's dependencies and storm following the guidance in the [website](https://github.com/Practical-Formal-Methods/storm). For example: 

```
cd storm
virtualenv --python=/usr/bin/python3 venv
source venv/bin/activate
python setup.py install
deactivate
```