# A Library for Testing SMT Solvers


## 1. The SMT-LIB2 formula generator

### Try the generator
The main generator is `fuzzlib/generators/smtfuzz.py`, which supports tens of SMT theories and different modes.
To run the generator, you only need a python interpreter (Python2 or Python3). 


Just type `python fuzzlib/generators/smtfuzz.py`, and you will see an SMT-LIB2 formula in the screen.


For more advanced options, please try `python fuzzlib/generators/smtfuzz.py -h`

### Use the generator as a library

We have provided an examples in `examples`:
- `examples/grammar_gen.py`: generate an SMT-LIB2 string (which can be assigned to a Python variable)


## 2. Build a fuzzer on top of the generator

Here, we provide an example of using the formula generator.
Suppose we need to test an SMT solver `solver_name`

We may use a bash script to invoke the generator and run the SMT solver under test.
~~~~
#!/bin/bash
#Generate 1000 files in /tmp. The log file records STDERR
rm -rf /tmp/test
mkdir /tmp/test
logfile=../test.log
echo "starting\n" >$logfile
for j in $(seq 1 1000); do
  tmpfile=/tmp/cvctest1/cvc$j.smt2
  echo $tmpfile
  echo $tmpfile >>$logfile
  python3 ./fuzzlib/generators/smtfuzz.py > $tmpfile 
  #You may have different choices of updating the log file
  #1. print stdout to logfile: > $logfile
  #2. print all info to logfile: $tmpfile >>$logfile 2>&1
  #3. pirnt steerr to logfile: 2>>$logfile
  timeout -s SIGKILL 5s /somepath/solver_name $tmpfile >>$logfile 2>&1
done
~~~~
