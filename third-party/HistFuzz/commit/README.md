## Commit Search Script

### Overview

This script automates the process of finding a specific commit in a project's version history that either induces or fixes a bug. The script is designed to perform binary search through the commit history to locate the desired commit.


### Prerequisites

- Python 3.x
- Git installed and accessible via command line
- Dependencies required for building the target project (`z3`, `cvc5`, etc.)

### Usage

The script can be run directly from the command line with the following syntax:

```bash
python3 commit_check.py <target_project> <message> <test_file> <commit_type> [--start_commit START] [--end_commit END]
```

#### Arguments


- **`target_project`**: Name of the target project (e.g., `z3`, `cvc5`).
- **`message`**: Message or pattern to search for in the test output to determine if the bug is present.
- **`test_file`**: Path to the test file that triggers the bug.
- **`commit_type`**: Specifies whether to search for a commit  `inducing` or `fixing` the bug. 
- **`--start_commit`** (optional): Specify the commit to start the search from.
- **`--end_commit`** (optional): Specify the commit to end the search at.

#### Example

```bash
python3 commit_check.py z3 "error message" test.smt2 inducing --start_commit abc1234 --end_commit xyz7890
```

### Notes

- The script is tailored for specific projects (`z3`, `cvc5`). For other projects, adjust the build commands accordingly.
- The script assumes a Linux environment with Bash shell and may require modifications to work on other operating systems.
