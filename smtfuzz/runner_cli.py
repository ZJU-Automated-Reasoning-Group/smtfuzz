"""
SMTFuzz Runner CLI - Advanced Fuzzing Modes

This tool provides seed-based and generation-based fuzzing capabilities.
For the original SMT formula generator, use the smtfuzz command.
"""

import sys
import argparse


def main():
    """Main entry point for the smtfuzz-runner command."""
    parser = argparse.ArgumentParser(
        description="SMTFuzz Runner - Advanced SMT Solver Fuzzing Tool",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Available modes:
  seed      Run seed-based fuzzing using existing SMT files
  gen       Run generation-based fuzzing creating new SMT formulas

Examples:
  smtfuzz-runner seed --seed /path/to/seeds --solver z3 --output /tmp/results
  smtfuzz-runner gen --solver cvc5 --logicmode bv --count 100

For more help on specific modes:
  smtfuzz-runner seed --help
  smtfuzz-runner gen --help

For the original SMT formula generator, use: smtfuzz --logic QF_BV --strategy cnf
        """
    )
    
    subparsers = parser.add_subparsers(dest='mode', help='Available modes')
    
    # Seed mode
    seed_parser = subparsers.add_parser('seed', help='Seed-based fuzzing')
    seed_parser.add_argument('--seed', required=True, help='Path to seed directory')
    seed_parser.add_argument('--solver', default='z3', help='Target solver')
    seed_parser.add_argument('--output', default='~/tmp/res/', help='Output directory')
    seed_parser.add_argument('--timeout', type=int, default=10, help='Timeout for each solving')
    seed_parser.add_argument('--count', type=int, default=50, help='Counts for each combination')
    seed_parser.add_argument('--workers', type=int, default=1, help='Number of threads')
    seed_parser.add_argument('--diff', default='no', help='Enable differential testing')
    seed_parser.add_argument('--perf', default='no', help='Enable performance testing')
    seed_parser.add_argument('--nomut', default='no', help='Disable mutation')
    seed_parser.add_argument('--solvers', default='no', help='Semicolon-separated solver list')
    seed_parser.add_argument('--solvermode', default='default', help='Solver mode')
    seed_parser.add_argument('--logicmode', default='default', help='Logic mode')
    seed_parser.add_argument('--optfuzz', default='no', help='Enable option fuzzing')
    seed_parser.add_argument('-v', '--verbose', action='store_true', help='Verbose output')
    seed_parser.add_argument('-p', '--profile', action='store_true', help='Profile mutation speed')
    
    # Gen mode
    gen_parser = subparsers.add_parser('gen', help='Generation-based fuzzing')
    gen_parser.add_argument('--solver', default='z3', help='Target solver')
    gen_parser.add_argument('--output', default='~/tmp/res/', help='Output directory')
    gen_parser.add_argument('--timeout', type=int, default=10, help='Timeout for each solving')
    gen_parser.add_argument('--count', type=int, default=50, help='Counts for each combination')
    gen_parser.add_argument('--workers', type=int, default=1, help='Number of threads')
    gen_parser.add_argument('--solvermode', default='default', help='Solver mode')
    gen_parser.add_argument('--logicmode', default='default', help='Logic mode')
    gen_parser.add_argument('--optfuzz', default='no', help='Enable option fuzzing')
    gen_parser.add_argument('--config', default='no', help='Configuration file')
    gen_parser.add_argument('-v', '--verbose', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    if not args.mode:
        parser.print_help()
        return
        
    if args.mode == 'seed':
        from .runner.seed_runner import SeedRunner
        
        # Convert args to the format expected by SeedRunner
        sys.argv = ['smtfuzz-seed']
        for key, value in vars(args).items():
            if key != 'mode' and value is not None:
                if isinstance(value, bool) and value:
                    sys.argv.append(f'--{key}')
                elif not isinstance(value, bool):
                    sys.argv.extend([f'--{key}', str(value)])
        
        runner = SeedRunner()
        runner.run()
        
    elif args.mode == 'gen':
        from .runner.gen_runner import GenRunner
        
        # Convert args to the format expected by GenRunner
        sys.argv = ['smtfuzz-gen']
        for key, value in vars(args).items():
            if key != 'mode' and value is not None:
                if isinstance(value, bool) and value:
                    sys.argv.append(f'--{key}')
                elif not isinstance(value, bool):
                    sys.argv.extend([f'--{key}', str(value)])
        
        runner = GenRunner()
        runner.run()


def cli_main():
    """Entry point for the smtfuzz-runner command."""
    main()


if __name__ == '__main__':
    cli_main() 