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


def saturation_with_tree(G: Sequent) -> ProofNode:
    root = ProofNode(sequent=closure(G))
    stack = [root]

    while stack:
        node = stack.pop()
        Gc = closure(node.sequent)
        node.sequent = Gc

        # Case 1: almost happy → leaf
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

p = Prop("p")
q = Prop("q")
r = Prop("r")
s = Prop("s")

x = Label("x")

F = And(
    Imp(Or(p, q), r),          # (p ∨ q) → r
    And(
        Or(p, q),              # (p ∨ q)
        And(
            Imp(r, Bot()),     # r → ⊥
            s                  
        )
    )
)

G = Sequent(
    relations=[Preorder(x, x)],
    formulas=[LFormula(x, F, Polarity.IN)]
)

tree = saturation_with_tree(G)
latex = export_proof_to_latex_document(tree)

with open("test.tex", "w") as f:
    f.write(latex)
print("Test was finished")