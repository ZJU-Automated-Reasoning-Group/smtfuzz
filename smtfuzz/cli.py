"""
SMTFuzz CLI - Legacy SMT Formula Generator

This is the original SMTFuzz generator for creating random SMT formulas.
For seed-based and generation-based fuzzing, use the smtfuzz-runner tool.
"""

import sys


def main():
    """Main entry point for the legacy smtfuzz command."""
    # Run legacy SMTFuzz directly
    from .smtfuzz import main as legacy_main
    legacy_main()


def cli_main():
    """Entry point for the smtfuzz command."""
    main()


if __name__ == '__main__':
    cli_main()
