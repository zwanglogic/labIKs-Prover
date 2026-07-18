from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROVER_DIR = ROOT / "prover"
if str(PROVER_DIR) not in sys.path:
    sys.path.insert(0, str(PROVER_DIR))

from syntax import And, Bot, Box, Diamond, Imp, Or, Prop  # noqa: E402

CONSTRUCTORS = {
    "Prop": Prop,
    "Bot": Bot,
    "And": And,
    "Or": Or,
    "Imp": Imp,
    "Box": Box,
    "Diamond": Diamond,
}
ARITY = {"Prop": 1, "Bot": 0, "And": 2, "Or": 2, "Imp": 2, "Box": 1, "Diamond": 1}
PROP_NAME_RE = re.compile(r"[A-Za-z][A-Za-z0-9]*\Z")


def parse_formula(source: str):
    """Parse the prover constructor language without eval()."""
    if not isinstance(source, str) or not source.strip():
        raise ValueError("Formula is required.")
    if len(source) > 4000:
        raise ValueError("Formula is too long.")

    try:
        tree = ast.parse(source.strip(), mode="eval")
    except SyntaxError as exc:
        raise ValueError(f"Syntax error near column {exc.offset or '?'}.") from exc

    node_count = 0

    def build(node: ast.AST, depth: int = 0):
        nonlocal node_count
        node_count += 1
        if node_count > 1000:
            raise ValueError("Formula contains too many nodes.")
        if depth > 100:
            raise ValueError("Formula nesting is too deep.")
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
            raise ValueError("Use constructors such as Prop('p'), Imp(...), Box(...).")

        name = node.func.id
        if name not in CONSTRUCTORS:
            raise ValueError(f"Unknown constructor: {name}")
        if node.keywords:
            raise ValueError("Keyword arguments are not supported.")
        expected = ARITY[name]
        if len(node.args) != expected:
            raise ValueError(f"{name} expects {expected} argument(s).")

        if name == "Prop":
            arg = node.args[0]
            if not isinstance(arg, ast.Constant) or not isinstance(arg.value, str):
                raise ValueError("Prop expects a quoted name, for example Prop('p').")
            value = arg.value.strip()
            if not PROP_NAME_RE.fullmatch(value):
                raise ValueError(
                    "Proposition names must start with a letter and contain only letters and digits."
                )
            if len(value) > 80:
                raise ValueError("Proposition names must contain at most 80 characters.")
            return Prop(value)

        args = [build(arg, depth + 1) for arg in node.args]
        return CONSTRUCTORS[name](*args)

    return build(tree.body)
