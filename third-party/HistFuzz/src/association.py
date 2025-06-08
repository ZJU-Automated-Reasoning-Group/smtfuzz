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


import random

from efficient_apriori import apriori
from src.building_blocks import BuildingBlocks
from src.utils.file_operation import get_smt_files_list
import os
import math


def association_analysis(seed_path_list, support, confidence):
    analysis_list = list()
    for path in seed_path_list:
        basic = BuildingBlocks(path)
        analysis_list.append(basic.basic_formula_tuple)
    itemsets, rules = apriori(analysis_list, min_support=support, min_confidence=confidence)
    return rules


def export_association_rules(file_path, output_path, sup, conf):
    # Check the type of file_path and obtain a list of files
    if isinstance(file_path, str):
        file_list = get_smt_files_list(file_path)
    elif isinstance(file_path, list):
        file_list = file_path
    
    # Get the total count of files
    file_count = len(file_list)
    
    # Calculate the support for association analysis
    sup = sup / file_count
    
    # Obtain the association rules
    rules = association_analysis(file_list, sup, conf)
    
    # Write the association rules to the output file
    with open(output_path, "w") as f:
        for r in rules:
            f.write(str(r) + "\n")
