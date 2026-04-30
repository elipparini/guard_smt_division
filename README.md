# guard_smt_division

A C program that rewrites SMT-LIB 2 files to guard division by zero.

## What it does

For every literal `L` in an assertion that contains a subterm `(/ num den)` where `den` is not a numeric constant, it replaces `L` with:

```
(and L (not (= den 0)))
```

## Requirements

- GCC (or any C11-compatible compiler)
- [Z3](https://github.com/Z3Prover/z3) C library and headers (`libz3-dev`)
- `pkg-config` (used by the Makefile to locate Z3)

## Building

```bash
make
```

## Usage

```bash
# Transform a single file
./guard_smt_division test_folder/div_test1.smt2

# Transform all .smt2 files in a directory (recursively)
./guard_smt_division test_folder
```

Output files are written under `nodiv/`, mirroring the input path. For example:

| Input | Output |
|-------|--------|
| `test_folder/div_test1.smt2` | `nodiv/test_folder/div_test1.smt2` |

