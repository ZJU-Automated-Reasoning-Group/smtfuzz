import argparse
import csv
import logging
import multiprocessing as mp
import os
import signal
import subprocess
from threading import Timer
from typing import List, Tuple


def terminate(process, is_timeout):
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as e:
            # pass
            print("error for interrupting: ", e)


def run_single_task(args: Tuple[List, int]) -> Tuple[str, str, float]:
    """Run a single test case with specified logic type and timeout"""
    status = "success"
    output = "None"
    execution_time = -1
    cmd, timeout = args  # unpack
    try:
        logging.debug(cmd)
        env = os.environ.copy()
        ptool = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
        is_timeout = [False]
        timertool = Timer(timeout, terminate, args=[ptool, is_timeout])
        timertool.start()
        output = ptool.stdout.readlines()
        output = ' '.join([str(element.decode('UTF-8')) for element in output])
        logging.debug(output)

        if is_timeout[0]:
            status = "timeout"
        if "error" in output:
            status = "error"

        ptool.stdout.close()
        timertool.cancel()
    except Exception as e:
        status = "failed"
    finally:
        print(status, output, execution_time)
        return status, output, execution_time


def get_cmdlist(csv_file_path, binary_tool_path):
    tasks = []
    with open(csv_file_path, mode='r') as csvfile:
        csv_reader = csv.DictReader(csvfile)
        for row in csv_reader:
            file_relative_path = row['file_relative_path']
            command = [binary_tool_path, file_relative_path]
            # for option, value in row.items():
            #    if option != 'file_relative_path' and value == '1':
            #        command.append(f'--{option}')
            tasks.append(command)
    return tasks


if __name__ == "__main__":
    # mp.cpu_count()
    parser = argparse.ArgumentParser(description='Test')
    parser.add_argument('--workers', type=int, default=1, help='Number of parallel workers')
    parser.add_argument('--timeout', type=int, default=10, help='Timeout in seconds')
    parser.add_argument('--log_level', choices=['DEBUG', 'INFO', 'WARNING', 'ERROR'], default='INFO',
                        help='Logging level')
    # parser.add_argument('--output', type=str, default='results.csv', help='Output CSV file')

    args = parser.parse_args()

    # Configure logging
    logging.basicConfig(level=getattr(logging, args.log_level))
    logger = logging.getLogger(__name__)

    pool = mp.Pool(args.workers)

    def signal_handler(sig, frame):
        pool.terminate()
        print("Exiting gracefully...")
        exit(0)


    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    cmd_lists = get_cmdlist("tmp.csv", "z3")

    test_params = [(cmd, args.timeout) for cmd in cmd_lists]
    logger.info(f"Starting {len(cmd_lists)} tasks with {args.workers} workers")
    results = pool.map(run_single_task, test_params)
    print(results)

    logger.info("finished!")
