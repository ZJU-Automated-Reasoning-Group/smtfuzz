#!/usr/bin/env python
from __future__ import division, print_function

import argparse
import mmap
import os
import shutil
import signal
import subprocess
import sys
import tempfile
from argparse import REMAINDER
from threading import Timer

import cup

"""
linedd is a delta-debugger for line-oriented text formats, used for minimizing inputs to programs while preserving errors.
In contrast to most delta-debuggers, linedd isn't specialized to deal with any particular syntax or format, beyond line endings.
It can be directly employed, without modification, to delta-debug any line-oriented text file. 

Given a system command of the form "command argument1 argument2 file", (with file as the last argument),
linedd will execute that command on the file and record the exit code. It will then repeatedly attempt to remove one or more individual lines
from the file, each time executing the original command on the new, smaller file. If the exit code of the command changes after removing
a line, linedd will backtrack, replacing the line and removing a new one. 
In this way it continues removing lines until it reaches a fixed point.
Usage is as simple as
$linedd <file_to_minimize> <output_file> "command arg1 arg2 arg3"
Where the file_to_minimize is the file you start with, and output_file is where linedd should write its minimzed version. Command is any arbitrary command, optionally with arguments.
Command will then be executed repeatedly as "command arg1 arg2 arg3 output_file". linedd assumes that the command expects the file as its last argument. 
"""


def terminate(process):
    if process.poll() is None:
        try:
            process.terminate()
        except Exception as e:
            print("error for interrupting")
            print(e)


def signal_handler(signal, frame):
    error_quit("\nlinedd terminated by interrupt signal.")


signal.signal(signal.SIGINT, signal_handler)


# Should linedd also catch keyboard interrupts from child processes?

class HelpParser(argparse.ArgumentParser):
    def error(self, message):
        sys.stderr.write('error: %s\n\n' % message)
        self.print_help()
        sys.exit(2)


parser = HelpParser(description="linedd: A line-oriented delta debugger.\nUsage: " + os.path.basename(
    sys.argv[0]) + " [options] <input_file> <output_file> command"
                                + "\n\nExample: If \"./buggy_program -buggyflag buggy_input.txt\" crashes with error code 139\n"
                                + os.path.basename(
    sys.argv[0]) + " buggy_input.txt minimized_input.txt ./buggy_program -buggyflag"
                                + "\nA minimized subset of \"buggy_input.txt\" that produces the same error code will be created and stored in \"minimized_input.txt\"."
                    , formatter_class=argparse.RawTextHelpFormatter, usage=argparse.SUPPRESS)

# positional arguments
parser.add_argument("infile",
                    help="Path to input file (this file will not be altered); this file will be appended to the command before it is executed")
parser.add_argument("outfile", help="Path to store reduced input file in")
# parser.add_argument("command", type=str, help="Command to execute (with the input file will be appended to the end). May include arguments to be passed to the command", nargs=argparse.REMAINDER, action="store")
parser.add_argument("command", type=str,
                    help="Command to execute (with the input file will be appended to the end). May include arguments to be passed to the command",
                    nargs=REMAINDER)

# optional arguments
parser.add_argument("--expect", type=int,
                    help="Expected exit code. If supplied, linedd will skip the initial execution of the command (default: None)",
                    default=None)

parser.add_argument('--signal', dest='signal', action='store_true',
                    help="Use the full unix termination-signal, instead of just the exit code (default: --no-signal)")
parser.add_argument('--no-signal', dest='signal', action='store_false', help=argparse.SUPPRESS)
parser.set_defaults(signal=False)

parser.add_argument('-q', '--quiet', dest='quiet', action='store_true',
                    help="Suppress progress information (default: --no-quiet)")
parser.add_argument('--no-quiet', dest='quiet', action='store_false', help=argparse.SUPPRESS)
parser.set_defaults(quiet=False)

parser.add_argument('-v', '--verbose', dest='verbose', action='store_true',
                    help="Show extra progress information (default: --no-verbose)")
parser.add_argument('--no-verbose', dest='verbose', action='store_false', help=argparse.SUPPRESS)
parser.set_defaults(verbose=False)

parser.add_argument('--reverse', dest='reverse', action='store_true',
                    help="Remove lines starting from the end of the file, rather than the beginning (default: --no-reverse)")
parser.add_argument('--no-reverse', dest='reverse', action='store_false', help=argparse.SUPPRESS)
parser.set_defaults(reverse=False)

parser.add_argument('--linear', dest='linear', action='store_true',
                    help="Only remove lines one-by-one, instead of applying a binary search (default: --no-linear)")
parser.add_argument('--no-linear', dest='linear', action='store_false', help=argparse.SUPPRESS)
parser.set_defaults(linear=False)

parser.add_argument("--first", type=int, help="Don't remove lines before this one  (default: 1)", default=1)
parser.add_argument("--last", type=int, help="Don't remove lines after this one (-1 for infinity)  (default: -1)",
                    default=-1)

parser.add_argument("--mmap", dest='mmap', action='store_true',
                    help="Read the input file using a memory-mapped file (disable if linedd is crashing) (default: true for 64-bit Python, false for 32-bit Python )")
parser.add_argument('--no-mmap', dest='mmap', action='store_false', help=argparse.SUPPRESS)
parser.set_defaults(mmap=(sys.maxsize > 2 ** 32))

parser.add_argument("--difftest", type=int, help="test diff (default: 0)", default=0)
parser.add_argument("--match-out", dest="match_out",
                    default=None,
                    help="match string in stdout to identify " \
                         "failing input (default: stdout output)")
parser.add_argument("--match-err", dest="match_err",
                    default=None,
                    help="match string in stderr to identify " \
                         "failing input (default: stderr output)")
parser.add_argument('--config', dest='config', default='no', type=str)

args = parser.parse_args()
if (args.first < 1):
    args.first = 1
if (args.last >= 0 and args.last <= args.first):
    print("Last line (%d) is not after the first line (%d) to reduce, aborting." % (args.first, args.last))
    sys.exit(0);

m_difftest = False
if args.difftest == 1: m_difftest = True
z3_tool = '/home/peisen/test/tofuzz/z3-debug/build/z3'
# cvc4_tool = '/home/peisen/test/tofuzz/CVC4-Release/build/bin/cvc4'
cvc4_tool = '/home/peisen/test/tofuzz/Bitwuzla-fixed/bin/bitwuzla'

first = args.first - 1  # Users usually expect line numbers in text files to be 1-based, not 0-based, so subtract one.
last = args.last - 1 if args.last > 0 else args.last
expect = args.expect
backward = args.reverse
linear = args.linear
use_signal = args.signal
quiet = args.quiet
verbose = args.verbose and not args.quiet

abortOnExistingFile = False
allowOverwritingBackups = True
use_mmap = args.mmap

if quiet:
    def print_out(*args, **kwargs):
        pass
else:
    def print_out(*args, **kwargs):
        print(*args, **kwargs)
        sys.stdout.flush()


def error_quit(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)
    sys.exit(1)


def usage_quit(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)
    print("Usage:\t linedd <file_to_minimize> <output_file> command")
    print(
        "\te.g., if \"./my_program --my_arg my_buggy_file\" exits with code 134, call\n\tlinedd my_buggy_file reduced_file ./my_program --my_arg")
    sys.exit(1)


infile = args.infile
if (not infile):
    error_quit("Could not read input file " + infile + ", aborting!");

basename, extension = os.path.splitext(infile)

# Check if the input file is executable; abort if it is. This check might only work on *nix:
if os.access(infile, os.X_OK):
    usage_quit("Input file " + infile + " is executable, aborting!")

try:
    original_open_file = open(infile, "r+b")
    if use_mmap:
        original_file = mmap.mmap(original_open_file.fileno(), 0, access=mmap.ACCESS_READ);
        n_original_lines = 0
        while original_file.readline():
            n_original_lines += 1
        if (n_original_lines == 0):
            error_quit("File contains no lines, aborting!")
        original_file.seek(0)
        # since I'm not sure if you can close the memory mapped file descriptor here,
        # I'm going to hold on to it until exit...
    else:
        original_lines = original_open_file.readlines()
        n_original_lines = len(original_lines)
        if (n_original_lines == 0):
            error_quit("File contains no lines, aborting!")
        original_open_file.close()
        original_open_file = None

except IOError as e:
    error_quit("Could not read input file " + infile + ", aborting!");

if (len(args.command) == 0):
    # This is a very common error - it usually means the user forgot to set an output file.

    error_quit(
        "No command specified, aborting.\nusage: linedd <inputfile> <outputfile> <command>" + "\n(output file was specified as " + str(
            args.outfile) + ")." if args.outfile else "");

command = " ".join(args.command)

outfile = args.outfile;

if (os.path.exists(outfile)):
    if (abortOnExistingFile):
        error_quit("Output file " + outfile + " already exists, aborting!")

    # Check if the output file is executable; abort if it is. This check might only work on *nix:
    if os.access(outfile, os.X_OK):
        usage_quit("Output file " + outfile + " is executable, aborting!")

    mfile = outfile + ".backup"
    if (os.path.exists(mfile)):
        mnum = 1
        while (mnum < 10 and os.path.exists(mfile + str(mnum))):
            mnum += 1
        mfile = mfile + str(mnum)
    if (os.path.exists(mfile) and not allowOverwritingBackups):
        error_quit("Output file " + outfile + " already exists, too many backups already made, aborting!");

    else:
        if os.path.exists(mfile):
            print_out(
                "Output file " + outfile + " already exists, too many backups already made, over-writing " + mfile + "!");
        else:
            print_out("Output file " + outfile + " already exists, moving to " + mfile);
        shutil.move(outfile, mfile)

    # Dangerous: I used cup from Baidu to set a timeotu


def run(filename):
    cmd = command + " " + filename
    shellexec = cup.shell.ShellExec()
    if (verbose):
        print_out("running: " + cmd)
        # retval = os.system(cmd + " 2>&1");
        retval = shellexec.run(cmd=cmd, timeout=10)['returncode']
        print_out("exit " + str(retval) + "(" + str(retval >> 8) + ")")
    else:
        # retval = shellexec.run(cmd=cmd, timeout=10)['returncode']
        retval = os.system(cmd + " >/dev/null 2>&1");
    sig_val = 0
    if not use_signal:
        sig_val = retval & 0xF
        retval = retval >> 8
    if sig_val == signal.SIGINT:
        # Convenience method to exit if the user interrupts it while the child is running.
        error_quit(
            "\nlinedd terminated by interrupt signal from child process (use --signal to prevent child process signals from terminating linedd).")
    return retval


'''            
def run(filename):
    cmd = command + " " + filename
    if(verbose):
        print_out("running: " + cmd)
        retval = os.system(cmd + " 2>&1");
        print_out("exit " + str(retval) + "(" + str(retval>>8) + ")")
    else:
        retval = os.system(cmd+ " >/dev/null 2>&1");
    sig_val=0    
    if not use_signal:
        sig_val = retval & 0xF
        retval = retval >> 8
    if sig_val == signal.SIGINT:
        #Convenience method to exit if the user interrupts it while the child is running.
        error_quit("\nlinedd terminated by interrupt signal from child process (use --signal to prevent child process signals from terminating linedd).")
    return retval
'''


def run_stderr(filename):
    ret = False
    errcmd = ['/home/peisen/test/tofuzz/z3-debug/build/z3']
    # errcmd = ['/home/peisen/test/tofuzz/CVC4/build/bin/cvc4']
    # errcmd.append('--produce-abducts'); errcmd.append('--incremental')
    # errcmd.append('timeout=10000')
    errcmd.append(filename)
    # logging.debug("z3 start to solve")
    # print(errcmd)
    p = subprocess.Popen(errcmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    timer = Timer(30, terminate, args=[p])
    timer.start()
    out = p.stdout.readlines()
    out = ' '.join([str(element.decode('UTF-8')) for element in out])
    if args.match_err:
        if args.match_err in out:
            print("stderr matching!")
            ret = True
    return ret


def run_diff(filename):
    ret = False

    cmd_z3 = [z3_tool];
    cmd_z3.append(filename)
    # logging.debug("z3 start to solve")
    pz3 = subprocess.Popen(cmd_z3, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    timerz3 = Timer(20, terminate, args=[pz3])
    timerz3.start()
    outz3 = pz3.stdout.readlines()
    outz3 = ' '.join([str(element.decode('UTF-8')) for element in outz3])
    # logging.debug(outz3)

    cmd_cvc4 = [cvc4_tool];
    cmd_cvc4.append('-i')
    cmd_cvc4.append(filename)
    # logging.debug("cvc4 start to solve")
    pcvc4 = subprocess.Popen(cmd_cvc4, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    timercvc4 = Timer(20, terminate, args=[pcvc4])
    timercvc4.start()
    outcvc4 = pcvc4.stdout.readlines()
    outcvc4 = ' '.join([str(element.decode('UTF-8')) for element in outcvc4])
    # logging.debug(outcvc4)

    z3_res = 'unknown'
    if not ('ASS' in outz3 or 'Ass' in outz3 or 'error' in outz3 or 'Add' in outz3):
        if 'unsat' in outz3:
            z3_res = 'unsat'
        elif 'sat' in outz3:
            z3_res = 'sat'

    cvc4_res = 'unknown'
    if not ('ASS' in outcvc4 or 'Ass' in outcvc4 or 'error' in outcvc4 or 'Add' in outcvc4):
        if 'unsat' in outcvc4:
            cvc4_res = 'unsat'
        elif 'sat' in outcvc4:
            cvc4_res = 'sat'

    print("z3, cvc: ", z3_res, cvc4_res)
    if z3_res != 'unknown' and cvc4_res != 'unknown':
        if z3_res != cvc4_res:
            print("find inconsistency!")
            ret = True

    return ret


print_out("Executing command: \"" + command + " " + infile + "\"")

skip_sanity = expect is not None  # If the user supplied an expected exit code, assume that they are doing so because the run is slow, so skip the sanity check too

if expect is None:
    expect = run(infile)

if (use_signal):
    print_out(
        "Expected exit code is " + str(expect) + " (value=" + str(expect >> 8) + ", signal=" + str(expect & 0xff) + ")")
else:
    print_out("Expected exit code is " + str(expect))

num_enabled = n_original_lines
enabled = [True] * num_enabled


def writeTo(filename):
    fout = open(filename, 'wb')
    if use_mmap:
        l = 0
        line = original_file.readline()
        while line:
            if (enabled[l]):
                fout.write(line)
            l += 1
            line = original_file.readline()
        original_file.seek(0)
    else:
        for l in range(n_original_lines):
            if (enabled[l]):
                fout.write(original_lines[l])
    fout.close()


# sanity check:
testingFile = tempfile.NamedTemporaryFile(delete=False, suffix=extension);
testingFileName = testingFile.name;
testingFile.close();

writeTo(testingFileName)
if not skip_sanity:
    ret = run(testingFileName)
    if (ret != expect):
        error_quit("Return value (" + str(
            ret) + ") of " + command + " " + testingFileName + " doesn't match expected value (" + str(
            expect) + "), even though no changes were made. Aborting!\n")

if last < 0:
    last = n_original_lines

if (first >= n_original_lines):
    error_quit("First line to minimize was " + str(first) + ", but file only has " + str(
        n_original_lines) + " lines, aborting.")

changed = True
round = 0
nremoved = 0
num_left = last - first

disabledSet = set()
# This executes a simple binary search, first removing half the lines at a time, then a quarter of the lines at a time, and so on until eventually individual lines are removed one-by-one.
while (changed):
    changed = False
    ntried = 0
    round += 1
    cur_removed = 0
    nsize = last - first - nremoved
    print_out("Round " + str(round) + ": Tried " + str(ntried) + ", Removed " + str(cur_removed) + "/" + str(nsize),
              end='')

    stride = num_left if not linear else 1
    while (stride >= 1):
        nfound = 0
        disabledSet.clear()
        for i in range(first, last) if not backward else range(first, last)[::-1]:
            if (enabled[i]):
                nfound += 1
                disabledSet.add(i)
                enabled[i] = False
                if (nfound == stride):
                    nfound = 0
                    ntried += 1
                    writeTo(testingFileName)
                    if m_difftest:
                        ret = run_diff(testingFileName)
                        if ret:  # diff
                            changed = True
                            writeTo(outfile)
                            num_enabled -= len(disabledSet)
                            num_left -= len(disabledSet)
                            nremoved += len(disabledSet)
                            cur_removed += len(disabledSet)
                            disabledSet.clear()
                        else:
                            for p in disabledSet:
                                enabled[p] = True
                            disabledSet.clear()
                    else:
                        run_res = False
                        if args.match_err:  # match stderr
                            run_res = run_stderr(testingFileName)
                        else:  # match only exist code
                            ret = run(testingFileName)
                            if ret == expect: run_res = True

                        if run_res:
                            changed = True
                            writeTo(outfile)
                            num_enabled -= len(disabledSet)
                            num_left -= len(disabledSet)
                            nremoved += len(disabledSet)
                            cur_removed += len(disabledSet)
                            disabledSet.clear()
                        else:
                            for p in disabledSet:
                                enabled[p] = True
                            disabledSet.clear()
                    print_out("\rRound " + str(round) + ": Tried " + str(ntried) + ", Removed " + str(
                        cur_removed) + "/" + str(nsize), end='')

        # If there are any remaining elements in the disabled set, then test them here.
        if (len(disabledSet) > 0):
            nfound = 0
            ntried += 1
            writeTo(testingFileName)
            ret = run(testingFileName)
            if (ret == expect):
                changed = True
                writeTo(outfile)
                num_enabled -= len(disabledSet)
                num_left -= len(disabledSet)
                nremoved += len(disabledSet)
                cur_removed += len(disabledSet)
                disabledSet.clear()
            else:
                for p in disabledSet:
                    enabled[p] = True
                disabledSet.clear()

            print_out(
                "\rRound " + str(round) + ": Tried " + str(ntried) + ", Removed " + str(cur_removed) + "/" + str(nsize),
                end='')

        assert (len(disabledSet) == 0);
        if (stride == 1):
            break

        stride = stride // 2
        assert (stride > 0)

    print_out("\rRound " + str(round) + ": Tried " + str(ntried) + ", Removed " + str(cur_removed) + "/" + str(nsize),
              end='\n')

# just in case this file got over-written at some point.
writeTo(outfile)
os.remove(testingFileName)
if original_open_file is not None:
    original_open_file.close();
print("Done. Kept " + str(num_enabled) + " lines, removed " + str(nremoved) + "/" + str(
    last - first) + " lines. Minimized file written to " + outfile + ".")

