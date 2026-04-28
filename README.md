# guard_smt_division

A Python script that rewrites SMT-LIB 2 files to guard division by zero.

## What it does

For every literal `L` in an assertion that contains a subterm `(/ num den)` where `den` is not a numeric constant, it replaces `L` with:

```
(and L (not (= den 0)))
```


## Requirements

- Python 3.10+
- [Z3](https://github.com/Z3Prover/z3) Python bindings (`pip install z3-solver`)

## Usage

```bash
# Transform a single file
python guard_smt_division.py test_folder/div_test1.smt2

# Transform all .smt2 files in a directory (recursively)
python guard_smt_division.py test_folder
```

Output files are written under `nodiv/`, mirroring the input path. For example:

| Input | Output |
|-------|--------|
| `test_folder/div_test1.smt2` | `nodiv/test_folder/div_test1.smt2` |

