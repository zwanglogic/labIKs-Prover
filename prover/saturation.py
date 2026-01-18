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

# dfs
def saturation(G : Sequent) -> list[Sequent]:
    stack = [closure(G)]
    leaves = []

    while stack:
        current_seq = closure(stack.pop())
        if is_almost_happy_sequent(current_seq):
            print(f"{current_seq} is almost happy")
            leaves.append(current_seq)
            continue

        outcome = apply_one_rule(current_seq, saturation_rules)

        # not almost happy and no rule applicable
        if outcome is None:
            raise RuntimeError(
                f"Saturation stuck (not almost happy, no rule applies):\n{current_seq}"
            )

        for child in outcome:
            stack.append(closure(child)) # do closure again, just in case
    
    return leaves

# saturation with proof tree visualization
def saturation_with_tree(G: Sequent) -> ProofNode:
    root = ProofNode(sequent=closure(G))
    stack = [root]

    while stack:
        current = stack.pop()
        current.sequent = closure(current.sequent)

        if is_almost_happy_sequent(current.sequent):
            continue

        applied = apply_one_rule_node(current, saturation_rules)

        if not applied:
            raise RuntimeError(
                f"Saturation stuck (not almost happy, no rule applies):\n{current.sequent}"
            )

        stack.extend(current.children)

    return root

# labels
x = Label("x")

# formulas
p = Prop("p")
q = Prop("q")
r = Prop("r")

phi = Or(And(p, q), r)

# initial sequent
G0 = Sequent(
    relations=[Preorder(x, x)],
    formulas=[LFormula(x, phi, Polarity.IN)]
)


root = saturation_with_tree(G0)

print_proof_tree(root)