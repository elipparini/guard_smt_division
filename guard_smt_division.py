#!/usr/bin/env python3
"""
Transform SMT2 files: for each literal L that contains a subterm of the form
(/ num den) where den is not a numeric constant, replace L with
(and L (not (= den 0))).

Usage:  python guard_smt_division.py <file.smt2|directory>
Output: nodiv/<relative/path/to/file.smt2>
"""

import re
import os
import sys
import z3


# ---------------------------------------------------------------------------
# SMT2 file splitting
# ---------------------------------------------------------------------------

def parse_smt2_commands(text: str) -> list[str]:
    """Split SMT2 source text into a list of top-level command strings."""
    commands: list[str] = []
    i, n = 0, len(text)

    while i < n:
        # Skip whitespace
        while i < n and text[i] in ' \t\n\r':
            i += 1
        if i >= n:
            break

        # Skip line comments
        if text[i] == ';':
            end = text.find('\n', i)
            i = end + 1 if end != -1 else n
            continue

        if text[i] != '(':
            i += 1
            continue

        # Scan to the matching closing parenthesis
        start = i
        depth = 0
        in_string = False
        in_comment = False

        while i < n:
            c = text[i]
            if in_comment:
                if c == '\n':
                    in_comment = False
            elif in_string:
                if c == '\\':
                    i += 1          # skip escaped character
                elif c == '"':
                    in_string = False
            elif c == ';':
                in_comment = True
            elif c == '"':
                in_string = True
            elif c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0:
                    commands.append(text[start:i + 1])
                    i += 1
                    break
            i += 1

    return commands


def get_command_name(cmd: str) -> str | None:
    m = re.match(r'\(\s*([^\s()]+)', cmd)
    return m.group(1) if m else None


# ---------------------------------------------------------------------------
# Z3 formula traversal helpers
# ---------------------------------------------------------------------------

def is_numeric_const(expr: z3.ExprRef) -> bool:
    """True if expr is a numeric literal (integer, rational, algebraic, or a
    to_real/to_int coercion of one)."""
    if z3.is_rational_value(expr) or z3.is_int_value(expr) or z3.is_algebraic_value(expr):
        return True
    if z3.is_app(expr) and expr.decl().name() in ('to_real', 'to_int') and expr.num_args() == 1:
        return is_numeric_const(expr.arg(0))
    return False


def get_non_const_dens(expr: z3.ExprRef) -> list[z3.ExprRef]:
    """Collect every non-constant denominator in division subterms of expr."""
    dens: list[z3.ExprRef] = []
    seen_ids: set[int] = set()

    def traverse(e: z3.ExprRef) -> None:
        eid = e.get_id()
        if eid in seen_ids:
            return
        seen_ids.add(eid)
        if z3.is_app(e):
            if e.decl().name() == '/':
                den = e.arg(1)
                if not is_numeric_const(den):
                    dens.append(den)
            for child in e.children():
                traverse(child)

    traverse(expr)
    return dens


def is_atom(expr: z3.ExprRef) -> bool:
    """True if expr is a boolean atom (not a propositional connective)."""
    if not z3.is_bool(expr):
        return False
    if (z3.is_and(expr) or z3.is_or(expr) or z3.is_not(expr)
            or z3.is_implies(expr) or z3.is_true(expr) or z3.is_false(expr)):
        return False
    if z3.is_quantifier(expr):
        return False
    # Treat boolean if-then-else as a connective
    if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_ITE:
        return False
    return True


def is_literal(expr: z3.ExprRef) -> bool:
    """True if expr is a literal: an atom or the negation of an atom."""
    if z3.is_not(expr):
        return is_atom(expr.arg(0))
    return is_atom(expr)


def make_nonzero_guard(den: z3.ExprRef) -> z3.BoolRef:
    """Build (not (= den 0)) with the correct numeric sort for zero."""
    ctx = den.ctx
    zero = z3.RealVal(0, ctx=ctx) if z3.is_real(den) else z3.IntVal(0, ctx=ctx)
    return z3.Not(den == zero)


# ---------------------------------------------------------------------------
# Formula transformation
# ---------------------------------------------------------------------------

def transform_formula(expr: z3.ExprRef) -> z3.ExprRef:
    """
    Recursively walk the boolean structure.  At each literal L that contains
    a division (/ · den) with a non-constant denominator, replace L with
    (and L (not (= den 0))).
    """
    if not z3.is_bool(expr):
        return expr

    # ---- literal: leaf of the boolean tree ----
    if is_literal(expr):
        dens = get_non_const_dens(expr)
        if not dens:
            return expr
        # Deduplicate by structural representation
        unique: dict[str, z3.ExprRef] = {}
        for d in dens:
            key = d.sexpr()
            if key not in unique:
                unique[key] = d
        guards = [make_nonzero_guard(d) for d in unique.values()]
        return z3.And(expr, *guards)

    # ---- propositional connectives: recurse ----
    if z3.is_and(expr):
        return z3.And(*[transform_formula(c) for c in expr.children()])
    if z3.is_or(expr):
        return z3.Or(*[transform_formula(c) for c in expr.children()])
    if z3.is_not(expr):
        # not(non-atom) — recurse inside
        return z3.Not(transform_formula(expr.arg(0)))
    if z3.is_implies(expr):
        return z3.Implies(
            transform_formula(expr.arg(0)),
            transform_formula(expr.arg(1)),
        )
    if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_ITE:
        return z3.If(
            transform_formula(expr.arg(0)),
            transform_formula(expr.arg(1)),
            transform_formula(expr.arg(2)),
        )

    # Quantifiers and unknown structures: leave unchanged
    return expr


# ---------------------------------------------------------------------------
# Per-assertion parse + transform
# ---------------------------------------------------------------------------

def transform_assert(ctx_commands: list[str], assert_cmd: str) -> str:
    """
    Parse *assert_cmd* in the context provided by *ctx_commands*, apply the
    transformation, and return the new (assert ...) string.
    Falls back to the original command on parse errors.
    """
    z3_ctx = z3.Context()
    full_smt = '\n'.join(ctx_commands) + '\n' + assert_cmd

    try:
        assertions = z3.parse_smt2_string(full_smt, ctx=z3_ctx)
    except z3.Z3Exception as exc:
        print(f"Warning: could not parse assertion, keeping original.\n  {exc}",
              file=sys.stderr)
        return assert_cmd

    if not assertions:
        return assert_cmd

    formula = (assertions[0]
               if len(assertions) == 1
               else z3.And(*list(assertions), ctx=z3_ctx))

    transformed = transform_formula(formula)
    return f"(assert {transformed.sexpr()})"


# ---------------------------------------------------------------------------
# File-level processing
# ---------------------------------------------------------------------------

# Commands that establish the declaration context used when parsing assertions
_CONTEXT_CMDS = {
    'set-logic', 'set-option', 'set-info',
    'declare-fun', 'declare-const', 'declare-sort',
    'define-fun', 'define-sort', 'define-const',
}

_TO_REAL_RE = re.compile(r'\(to_real (\d+)\)')


def simplify_to_real(text: str) -> str:
    """Replace (to_real N) where N is a non-negative integer literal with N.0"""
    # Repeat until no more matches (handles nesting, though z3 doesn't produce it)
    while True:
        new = _TO_REAL_RE.sub(lambda m: m.group(1) + '.0', text)
        if new == text:
            return text
        text = new


def transform_file(input_path: str) -> str:
    """Read *input_path*, transform all assertions, return the result."""
    with open(input_path, 'r') as fh:
        text = fh.read()

    commands = parse_smt2_commands(text)
    ctx_commands: list[str] = []
    result: list[str] = []

    for cmd in commands:
        name = get_command_name(cmd)
        if name in _CONTEXT_CMDS:
            ctx_commands.append(cmd)
            result.append(cmd)
        elif name == 'assert':
            result.append(simplify_to_real(transform_assert(ctx_commands, cmd)))
        else:
            result.append(cmd)

    return '\n'.join(result) + '\n'


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def process_file(input_path: str) -> None:
    output_path = os.path.join('nodiv', input_path)
    output_dir = os.path.dirname(output_path)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    result = transform_file(input_path)

    with open(output_path, 'w') as fh:
        fh.write(result)

    print(f"Written: {output_path}")


def main() -> None:
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <file.smt2|directory>", file=sys.stderr)
        sys.exit(1)

    input_path = sys.argv[1]

    if os.path.isfile(input_path):
        process_file(input_path)
    elif os.path.isdir(input_path):
        smt2_files = sorted(
            os.path.join(root, fname)
            for root, _dirs, files in os.walk(input_path)
            for fname in files
            if fname.endswith('.smt2')
        )
        if not smt2_files:
            print(f"No .smt2 files found in {input_path!r}", file=sys.stderr)
            sys.exit(1)
        for path in smt2_files:
            process_file(path)
    else:
        print(f"Error: {input_path!r} is not a file or directory", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
