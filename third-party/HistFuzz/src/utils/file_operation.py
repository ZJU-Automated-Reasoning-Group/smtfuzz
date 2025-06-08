"""
MIT License

Copyright (c) 2023 The histfuzz authors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""


import pathlib
import shutil
import os
import copy


def get_all_smt2_file(path):
    file_path = pathlib.Path(path).rglob("*.smt2")
    return file_path


def get_smt_files_list(path_to_directory, solver1=None, solver2=None):
    file_paths = list()
    if "bitwuzla" in [solver1, solver2]:
        logics = ["QF_ABV/", "QF_ABVFP/", "QF_ABVFPLRA/", "QF_AUFBV/", "QF_AUFBVFP/", "QF_BV/", "QF_BVFP/",
                  "QF_BVFPLRA/", "QF_FP/", "QF_FPLRA/", "QF_UFBV/", "QF_UFFP/", "bitwuzla/"]
        for r, d, f in os.walk(path_to_directory):
            for file in f:
                if ".smt20" in file:
                    continue
                if ".smt2" in file:
                    if "DT" not in r and select_logics(logics, r):
                        file_paths.append(os.path.join(r, file))
    else:
        for r, d, f in os.walk(path_to_directory):
            for file in f:
                if ".smt20" in file:
                    continue
                if ".smt2" in file:
                    if "DT" not in r:
                        file_paths.append(os.path.join(r, file))

    return file_paths


def select_logics(logics, file_path):
    for logic in logics:
        if logic in file_path:
            return True

    return False


def get_txt_files_list(path_to_directory):
    file_paths = list()
    for r, d, f in os.walk(path_to_directory):
        for file in f:
            if ".txt" in file:
                file_paths.append(os.path.join(r, file))

    return file_paths


def export_smt2_file(path, content):
    f = open(path, "w")
    f.write(content)


def copy_file(srcfile, dstpath):
    if not os.path.isfile(srcfile):
        print("%s not exist!" % (srcfile))
    else:
        fpath, fname = os.path.split(srcfile)
        if not os.path.exists(dstpath):
            os.makedirs(dstpath)
        shutil.copy(srcfile, dstpath + fname)
        # print("copy %s -> %s" % (srcfile, dstpath + fname))


def record_bug(temp, bug_type, buggy_mutant_path1, buggy_mutant_path2, solver1=None, result1=None, solver2=None,
               result2=None, option=None):
    # Set the directory to store temporary files
    temp_dir = temp
    # Create the directory if it doesn't exist
    if not os.path.exists(temp_dir):
        os.mkdir(temp_dir)

    # Set the path to store the bug folder
    path_to_bug_folder = os.path.join(temp_dir, bug_type)
    print("Creating a bug folder at: " + path_to_bug_folder)

    # Create the bug folder if it doesn't exist
    if not os.path.exists(path_to_bug_folder):
        os.mkdir(path_to_bug_folder)

    # Determine the number of subdirectories within the bug folder
    number_of_directories = 0
    for r, d, f in os.walk(path_to_bug_folder):
        number_of_directories = len(d)
        break

    # Set the path to create a new subdirectory within the bug folder
    path_to_bug_dir = os.path.join(path_to_bug_folder, str(number_of_directories))

    # Create the new subdirectory
    os.mkdir(path_to_bug_dir)

    # Copy the original file and the mutant to the bug subdirectory
    shutil.copy2(buggy_mutant_path1, path_to_bug_dir)
    shutil.copy2(buggy_mutant_path2, path_to_bug_dir)

    # Create a string to store information about the bug
    error_logs = "Some info on this bug:\n"
    error_logs += bug_type + "\n"
    if isinstance(result1, list):
        result1 = "".join(result1)
    if isinstance(result2, list):
        result2 = "".join(result2)
    if solver1 and result1:
        error_logs += solver1 + " return " + result1 + "\n"
    if solver2 and result2:
        error_logs += solver2 + " return " + result2 + "\n"
    if option is not None:
        error_logs += "\n" + "The chosen option: " + option + "\n"
    error_logs += "\n"

    # Write the bug information to a file within the bug subdirectory
    create_file(error_logs, os.path.join(path_to_bug_dir, "error_logs.txt"))


def create_file(data, path):
    file = open(path, "w")
    file.write(data)
    file.close()


def export_smt2(script, direct, index):
    if not os.path.exists(direct):
        os.mkdir(direct)
    file_path = direct + "/case" + str(index) + ".smt2"
    f = open(file_path, "w")
    f.write(script)
    # f.write("\n(check-sat)\n")
    f.close()
    return file_path



def reduce_duplicate(path1, path2):
    index_1 = 63
    while os.path.exists(path1 + "/" + str(index_1)):
        file_path_1 = set()
        index_2 = 0
        for r, d, f in os.walk(path1 + "/" + str(index_1)):
            for file in f:
                file_path_1.add(file)
        while os.path.exists(path2 + "/" + str(index_2)):
            file_path_2 = set()
            for r, d, f in os.walk(path2 + "/" + str(index_2)):
                for file in f:
                    file_path_2.add(file)
            if file_path_2 == file_path_1:
                file_set = file_path_2
                while len(file_set) > 0:
                    interest_file = file_set.pop()
                    if "case" in interest_file and "_t" not in interest_file:
                        break
                f1 = open(path1 + "/" + str(index_1) + "/" + interest_file, "r")
                f1_content = f1.read()
                f1.close()
                f2 = open(path2 + "/" + str(index_2) + "/" + interest_file, "r")
                f2_content = f2.read()
                f2.close()
                if f1_content == f2_content:
                    shutil.rmtree(path1 + "/" + str(index_1))
                    print("remove ", path1 + "/" + str(index_1))
                    break
            index_2 += 1
        index_1 += 1


def reduce_invalid(path):
    path_dic = dict()
    for r, d, f in os.walk(path):
        path_dic[r] = f
    for k in path_dic.keys():
        if len(path_dic[k]) != 0:
            log = open(k + "/error_logs.txt", "r")
            content = log.read()
            log.close()
            if "cvc5 return error" in content:
                for case in path_dic[k]:
                    if "case" in case and "_" not in case:
                        formula = open(k + "/" + case, "r")
                        fo = formula.read()
                        formula.close()
                        if "exp" in fo:
                            print("contain approximation")
                            shutil.rmtree(k)
                            print("remove: ", k)
                        break


if __name__ == "__main__":
    # reduce_duplicate("/foundbug/12-21/InvalidModel", "/foundbug/12-21/soundness")
    reduce_invalid("/foundbug/12-19/InvalidModel")
