"""
TBD: different modes
- Generation: the current one (based on smtfuzz.py)
- Mutation: use the code in mutators
"""

from .smtfuzz import *


def cli_main():
    """Entry point for the smtfuzz command."""
    print("SMTFuzz - A fuzzer for SMT solvers")
    main()


if __name__ == '__main__':
    # if len(sys.argv) > 1 and sys.argv[1] == 'smtfuzz':
    #    mutate_main()
    # else:
    #    cli_main()
    cli_main()
