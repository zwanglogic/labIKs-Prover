from syntax import *
from happy import *
from closure import *
from rules import *
from prooftree import *


saturation_rules = [
    rule_and_in,
    rule_and_out,
    rule_or_in,
    rule_or_out,
    rule_imp_in
]

# Saturation with visualization
def saturation_with_tree(G: Sequent) -> ProofNode:
    root = ProofNode(sequent=closure(G))
    stack = [root]

    while stack:
        node = stack.pop()
        Gc = closure(node.sequent)
        node.sequent = Gc

        # Case 1: almost happy 
        if is_almost_happy_sequent(Gc):
            continue

        # Case 2: try to make progress
        result = try_apply_rule(Gc, saturation_rules)

        if result is None:
            raise RuntimeError(
                f"Saturation stuck (not almost happy, no progress):\n{Gc}"
            )

        node.rule = getattr(try_apply_rule, "__last_rule_name__", None)

        # Case 2a: branch closed
        if result == []:
            node.children = []
            continue

        # Case 2b: genuine expansion
        children = []
        for seq in result:
            child = ProofNode(sequent=seq)
            children.append(child)

        node.children = children
        stack.extend(children)

    return root

# Saturation without visualization
def saturate(G: Sequent) -> list[Sequent]:
    initial = closure(G)
    stack = [initial]
    saturated: list[Sequent] = []

    while stack:
        Gc = closure(stack.pop())

        # Case 1: almost happy 
        if is_almost_happy_sequent(Gc):
            if Gc not in saturated:
                saturated.append(Gc)
            continue

        # Case 2: try to expand
        result = try_apply_rule(Gc, saturation_rules)

        if result is None:
            raise RuntimeError(
                f"Saturation stuck (not almost happy, no progress):\n{Gc}"
            )

        # Case 2a: axiom
        if result == []:
            if Gc not in saturated:
                saturated.append(Gc)
            continue

        # Case 2b: genuine expansion
        for seq in result:
            stack.append(seq)

    return saturated