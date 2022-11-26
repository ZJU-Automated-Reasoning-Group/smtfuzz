# A Library for Testing SMT Solvers

Contact: `pyaoaa@zju.edu.cn`

## The SMT-LIB2 formula generator

### Try the generator
The main generator is `fuzzlib/generators/smtfuzz.py`, which supports tens of SMT theories and different modes.
To run the generator, you only need a python interpreter (Python2 or Python3). 


Just type `python fuzzlib/generators/smtfuzz.py`, and you will see an SMT-LIB2 formula in the screen.


For more advanced options, please try `python fuzzlib/generators/smtfuzz.py -h`

### Using the generator as a library
See `examples/grammar_gen.py` for an example.


## The SMT-LIB2 formula mutator

Current, we implement an example in `fuzzlib/mutators/cube_mut` (NOTE: it relies
on Z3's Python API)
