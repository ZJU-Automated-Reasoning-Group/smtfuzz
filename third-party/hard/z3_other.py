'''
def readfile(filename):
    with open(filename,"r") as file:
        for line in file:
            line=line.strip()
            tokens=line.split()
            new_tokens=tokens+[str(60)]
            new_line="\t".join(new_tokens)+"\n"
            f=open("SMT-generator/5_test.txt","a")
            f.write(new_line)
            f.close()

if __name__=="__main__":
    readfile("SMT-generator/example_30.txt")
'''
import subprocess
import time
from multiprocessing import Pool, freeze_support
import numpy as np
import generator_bv
import shutil
import os


def solve_smt2_file(smt2_filename):
    try:
        # command = ["E:/SMT/mathsat/bin/mathsat.exe", smt2_filename]
        # command = ["D:/Downloads/yices-2.6.5-x86_64-unknown-mingw32-static-gmp/yices-2.6.5/bin/yices-smt2.exe", smt2_filename]
        command = ["D:/Downloads/cvc5-Win64-x86_64-static", smt2_filename]
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

        if result.returncode == 0:
            return True, result.stdout
        else:
            return False, result.stderr
    except Exception as e:
        return False, str(e)


def timeout_check_smt_file(filename):
    with Pool(processes=1) as pool:
        try:
            res = pool.apply_async(solve_smt2_file, (filename,))
            return res.get(timeout=60)  # 1分钟超时
        except:
            return None


def gtime(filename):
    start = time.time()
    res = timeout_check_smt_file(filename)
    end = time.time()
    if res is not None:
        solve_time = end - start
        return solve_time
    else:
        return 60

# if __name__ == "__main__":

# with open("SMT-generator/sort.txt","r") as file:
#     num=0
#     for line in file:
#         num+=1
#         line=line.strip()
#         tokens=line.split()
#         smt2_filename=tokens[0]
#         print(smt2_filename)
#         if num>0:
#             file_time=gtime(smt2_filename)
#             f=open("SMT-generator/QF_BV_others.txt","a")
#             f.write(smt2_filename+"\t"+str(file_time)+"\n")
#             f.close()

# dir="SMT-generator/seeds_real"
# files=os.listdir(dir)
# for file in files:
#     file_time=gtime(file)
#     print(file_time)
#     f=open("real_time_yices","a")
#     f.write(file+"\t"+str(file_time)+"\n")
#     f.close()
