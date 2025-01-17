#!/usr/bin/env python3
# smtfuzz/cli.py
from .smtfuzz import *

def cli_main():
    """Entry point for the smtfuzz command."""
    print("SMTFuzz - A fuzzer for SMT solvers")
    main()
    
if __name__ == '__main__':
    cli_main()