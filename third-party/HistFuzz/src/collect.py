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


import os
import re

import github3


def check_title(title: str):
    key_word = ["oundness", "bug", "issue", "Issue", "onsolidat", "olution", "invalid", "Invalid", "egfault", "orrect",
                "ssertion", "failure", "after-free", "leak", "verflow", "use after free"]
    for k in key_word:
        if k in title:
            return True

    return False


def collect_buggy_formula(github_token, solver, stored_dir):
    # authenticate with GitHub
    github = github3.login(token=github_token)
    if github is None:
        print("Token is invalid!\n Please check")
        return

    # set up repository information
    solver_repo = {"z3": "Z3Prover", "cvc5": "cvc5", "yices2": "SRI-CSL", "opensmt": "usi-verification-and-security",
                   "cvc5-projects": "cvc5"}
    repo = github.repository(solver_repo[solver], solver)

    # retrieve closed issues
    issues_list = repo.issues(state="closed")

    # create directory to store formulas
    stored_dir = stored_dir + "/" + solver
    if not os.path.exists(stored_dir):
        os.makedirs(stored_dir)

    print("updating " + solver + "......")

    for issue in issues_list:
        try:
            if check_title(issue.title):
                print(issue.number, " ", issue.title)
                count = 0
                if issue.body is not None:
                    if "```" in issue.body or "~~~~" in issue.body:
                        # extract formula from issue body
                        buggy_formula = extract_formula(issue.body)
                        if buggy_formula != "":
                            file_name = stored_dir + "/" + solver + "_" + str(issue.number) + "_" + str(count) + ".smt2"
                            # check if formula already exists, skip if it does
                            if os.path.exists(file_name):
                                return
                            else:
                                # save formula to file
                                output = open(file_name, "w")
                                output.write(buggy_formula)
                                output.close()
                                count = count + 1

                # retrieve comments
                if issue.comments_count != 0:
                    comments_iter = issue.comments()
                    for comment in comments_iter:
                        if comment.body is not None:
                            if "```" in comment.body or "~~~~" in comment.body:
                                # extract formula from comment
                                buggy_formula = extract_formula(comment.body)
                                if buggy_formula != "":
                                    file_name = stored_dir + "/" + solver + "_" + str(issue.number) + "_" + str(
                                        count) + ".smt2"
                                    # check if formula already exists, skip if it does
                                    if os.path.exists(file_name):
                                        return
                                    else:
                                        # save formula to file
                                        output = open(file_name, "w")
                                        output.write(buggy_formula)
                                        output.close()
                                        count = count + 1
        except:
            pass

import re


def extract_formula(con):
    # Initialize potential formula and final formula strings
    potential_formula = None
    formula = ""
    
    # Check if the content contains markdown-style code blocks
    if "```" in con:
        potential_formula = con.split("```")
    elif "~~~~" in con:
        potential_formula = con.split("~~~~")
    
    # If markdown-style code blocks are present
    if potential_formula is not None:
        for content in potential_formula:
            if "(check-sat" in content:
                # Find the first occurrence of any of the following keywords: (set, (define, (declare, (assert, cat <file>.smt2
                index_1 = re.search(r"\(set", content)
                index_2 = re.search(r"\(define", content)
                index_3 = re.search(r"\(declare", content)
                index_4 = re.search(r"\(assert", content)
                index_5 = re.search(r"cat\s+\S+\.smt2", content)
                
                # Determine the start and end positions of the formula content
                min_index = None
                if index_1 is not None:
                    min_index = index_1.span()[0]
                if index_2 is not None:
                    if min_index is None:
                        min_index = index_2.span()[0]
                    elif index_2.span()[0] < min_index:
                        min_index = index_2.span()[0]
                if index_3 is not None:
                    if min_index is None:
                        min_index = index_3.span()[0]
                    elif index_3.span()[0] < min_index:
                        min_index = index_3.span()[0]
                if index_4 is not None:
                    if min_index is None:
                        min_index = index_4.span()[0]
                    elif index_4.span()[0] < min_index:
                        min_index = index_4.span()[0]
                if index_5 is not None:
                    if min_index is None:
                        min_index = index_5.span()[1]
                    elif index_5.span()[1] > min_index:
                        min_index = index_5.span()[1]
                if min_index is None:
                    min_index = 0
                
                # Add the formula content to the final formula string
                formula = formula + content[min_index:] + "\n"
    
    # Return the final formula string
    return formula


def check_ref(issue):
    events = issue.events()
    for e in events:
        if e.event == "referenced":
            return True
    return False

