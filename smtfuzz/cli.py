"""
SMTFuzz CLI with multiple modes:
- Generation: the current one (based on smtfuzz.py)
- Mutation: use the code in mutators (bet/)
- Inter-theory: new inter-theory mutation engine (inter/)
"""

import sys
from .smtfuzz import *


def cli_main():
    """Entry point for the smtfuzz command."""
    # Check if inter-theory mode is requested
    if len(sys.argv) > 1 and sys.argv[1] == 'inter':
        # Remove 'inter' from args and call inter-theory CLI
        sys.argv = [sys.argv[0]] + sys.argv[2:]
        from .inter.cli import main as inter_main
        inter_main()
    elif len(sys.argv) > 1 and sys.argv[1] == 'mutate':
        # Remove 'mutate' from args and call mutation CLI
        sys.argv = [sys.argv[0]] + sys.argv[2:]
        from .bet.bet_mutator import main as mutate_main
        mutate_main()
    else:
        # Default generation mode
        print("SMTFuzz - A fuzzer for SMT solvers")
        print("Modes: generation (default), mutate, inter")
        main()


def main():
    """Main entry point for the package."""
    cli_main()


if __name__ == '__main__':
    cli_main()
