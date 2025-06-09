import time
from z3 import *
from multiprocessing import Pool
from multiprocessing import freeze_support


def check_smt_file(filename):
    s = Solver()
    with open(filename, 'r') as f:
        s.from_string(f.read())
    try:
        res = s.check()
        return res
    except:
        return None


def timeout_check_smt_file(filename):
    with Pool(processes=1) as pool:
        try:
            res = pool.apply_async(check_smt_file, (filename,))
            return res.get(timeout=1200)  # 1min
        except:
            return None


freeze_support()


def gtime(filename):
    start = time.time()
    res = timeout_check_smt_file(filename)
    end = time.time()
    if res is not None:
        solve_time = end - start
        return solve_time
    else:
        return 1200
