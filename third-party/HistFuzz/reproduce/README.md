# **Reproduce**

This is a Python script to reproduce the results of code coverage evaluation.

In the docker container, you can directly conduct the evaluation using `python3 script.py`.


If you build this project from source, you should modify the parameters in the [script](script.py), including 
```
z3_folder = <The directory of z3>
cvc5_folder = <The directory of cvc5>
z3_bin = <The path of z3 binary>
cvc5_bin = <The path of cvc5 binary>
```