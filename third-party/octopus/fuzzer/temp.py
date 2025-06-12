from z3 import *


def get_unsat_core(smt2_file):
    """Assert constraint `a` and track it in the unsat core using the Boolean constant `p`.

    If `p` is a string, it will be automatically converted into a Boolean constant.

    x = Int('x')
    p3 = Bool('p3')
    s = Solver()
    s.set(unsat_core=True)
    s.assert_and_track(x > 0,  'p1')
    s.assert_and_track(x != 1, 'p2')
    s.assert_and_track(x < 0,  p3)
    print(s.check())
    unsat
    c = s.unsat_core()
    len(c)
    2
    Bool('p1') in c
    True
    Bool('p2') in c
    False
    p3 in c
    True
    """
    s = Solver()
    s.set(unsat_core=True)
    with open(smt2_file, "r") as f:
        s.from_string(f.read())
    

