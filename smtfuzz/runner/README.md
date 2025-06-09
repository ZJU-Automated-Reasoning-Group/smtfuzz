# SMTFuzz Runner Module

This module contains the reorganized and refactored fuzzing runners for SMTFuzz. The code has been extracted and cleaned up from the original `driver_gen.py` and `driver_seed.py` files to eliminate redundancy and improve maintainability.

## Structure

### Base Classes

- **`base.py`**: Contains the `BaseRunner` class with common functionality shared between all runners:
  - Configuration loading
  - Black list management
  - Process termination handling
  - Signal handling
  - Statistics tracking
  - Common argument parsing

### Runners

- **`seed_runner.py`**: Implements seed-based fuzzing using existing SMT files
- **`gen_runner.py`**: Implements generation-based fuzzing creating new SMT formulas

## Usage

### Command Line Tools

Three command-line tools are provided:

1. **`smtfuzz`**: Unified interface with subcommands
2. **`smtfuzz-seed`**: Direct access to seed-based fuzzing
3. **`smtfuzz-gen`**: Direct access to generation-based fuzzing

### Examples

#### Seed-based Fuzzing
```bash
# Using the unified interface
smtfuzz seed --seed /path/to/seeds --solver z3 --output /tmp/results

# Using the direct tool
smtfuzz-seed --seed /path/to/seeds --solver z3 --output /tmp/results

# Differential testing
smtfuzz seed --seed /path/to/seeds --diff yes --solvers "z3;cvc5"

# Performance testing
smtfuzz seed --seed /path/to/seeds --perf yes --workers 4
```

#### Generation-based Fuzzing
```bash
# Using the unified interface
smtfuzz gen --solver cvc5 --logicmode bv --count 100

# Using the direct tool
smtfuzz-gen --solver cvc5 --logicmode bv --count 100

# With configuration file
smtfuzz gen --config /path/to/config.ini --workers 8
```

## Key Improvements

### Eliminated Redundancies

The original `driver_gen.py` and `driver_seed.py` files contained significant code duplication:

1. **Configuration loading**: Both files loaded `test_config.json` identically
2. **Black list handling**: Identical black list loading and checking logic
3. **Process management**: Same timeout and termination handling
4. **Signal handling**: Duplicate signal handler setup
5. **Solver path resolution**: Same `get_smt_solver_path` function
6. **Statistics tracking**: Similar statistics classes
7. **Z3 mutation**: Identical `try_z3_mutate` functions

### Improved Organization

- **Separation of concerns**: Base functionality separated from specific runner logic
- **Inheritance hierarchy**: Common functionality in base class, specific features in subclasses
- **Modular design**: Each runner focuses on its specific fuzzing approach
- **Consistent interfaces**: Standardized argument parsing and configuration

### Enhanced Usability

- **Unified CLI**: Single entry point with subcommands
- **Better help**: Comprehensive help messages and examples
- **Flexible deployment**: Multiple ways to invoke the tools
- **Improved error handling**: Better error messages and graceful failures

## Configuration

The runners use the same configuration system as the original drivers:

- **`test_config.json`**: Solver path configuration
- **Black list files**: Error filtering configuration
- **Command line arguments**: Runtime configuration

## Migration from Legacy Drivers

To migrate from the old drivers:

### From `driver_seed.py`
```bash
# Old way
python examples/driver_seed.py --seed /path/to/seeds --solver z3

# New way
smtfuzz seed --seed /path/to/seeds --solver z3
# or
smtfuzz-seed --seed /path/to/seeds --solver z3
```

### From `driver_gen.py`
```bash
# Old way
python examples/driver_gen.py --solver cvc5 --logicmode bv

# New way
smtfuzz gen --solver cvc5 --logicmode bv
# or
smtfuzz-gen --solver cvc5 --logicmode bv
```

## Development

### Adding New Runners

To add a new runner:

1. Create a new file in the `runner` directory
2. Inherit from `BaseRunner`
3. Implement the `run()` method
4. Add any specific argument parsing in `setup_args()`
5. Update `__init__.py` to export the new runner

### Extending Base Functionality

Common functionality should be added to `BaseRunner` in `base.py` to benefit all runners.

## Dependencies

The runners maintain the same dependencies as the original drivers:

- `tqdm`: Progress bars
- `smtfuzz.mutators.op_mutator`: String mutation
- `smtfuzz.mutators.bet_mutator`: Z3-based mutation (optional)

## Testing

The runners can be tested using the same test cases as the original drivers, but with the new command-line interface. 