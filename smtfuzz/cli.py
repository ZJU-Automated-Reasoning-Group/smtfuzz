"""
SMTFuzz CLI with multiple modes:
- Generation: the current one (based on smtfuzz.py)
- Mutation: use the code in mutators (bet/)
- Inter-theory: new inter-theory mutation engine (inter/)
"""

import sys
from .smtfuzz import main


def cli_main():
    """Entry point for the smtfuzz command."""
    main()


if __name__ == '__main__':
    cli_main()
