import re
import os
import random
import shutil



def recursively_get_files(path: str, extension: str):
    """
    Recursively get all files with a specified extension in a directory.

    Args:
        path (str): The path to the directory.
        extension (str): The file extension.

    Returns:
        List[str]: A list of file paths.
    """
    import os

    files = []
    for dirpath, _, filenames in os.walk(path):
        for filename in filenames:
            if filename.endswith(extension):
                files.append(os.path.join(dirpath, filename))
    return files

def extract_comments(filename):
    with open(filename, 'r') as file:
        content = file.read()

    pattern = r"(//.*?$|/\*.*?\*/)"
    comments = re.findall(pattern, content, re.MULTILINE | re.DOTALL)

    return comments

def eliminate_duplicate_lines(comments):
    unique_comments = []
    for comment in comments:
        if comment not in unique_comments:
            unique_comments.append(comment)
    return unique_comments

def get_all_files_recursively(path_to_directory):
    file_paths = list()
    for r, d, f in os.walk(path_to_directory):
        for file in f:
            file_path = os.path.join(r, file)
            file_paths.append(file_path)
    return file_paths

def get_all_smt_files_within_size(path_to_directory, size=1000000):
    file_paths = list()
    for r, d, f in os.walk(path_to_directory):
        for file in f:
            if file.endswith(".smt2"):
                file_path = os.path.join(r, file)
                if os.path.getsize(file_path) <= size:
                    file_paths.append(file_path)
    return file_paths

