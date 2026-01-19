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

def saturation_tree(G: Sequent) -> ProofNode:
    
    root = ProofNode(sequent=closure(G))
    stack = [root]

    while stack:
        current_node = stack.pop()
        current_seq = closure(current_node.sequent)

        # Case 1: leaf
        if is_almost_happy_sequent(current_seq):
            current_node.rule = None
            current_node.children = []
            continue

        # Case 2: apply one saturation rule
        result = apply_one_rule_tree(current_seq, saturation_rules)

        if result is None:
            # This should not happen if definitions are correct
            raise RuntimeError(
                "Saturation stuck: not almost happy, no rule applicable"
            )

        rule_name = apply_one_rule_tree.__last_rule_name__ \
            if hasattr(apply_one_rule_tree, "__last_rule_name__") \
            else "rule"

        current_node.rule = rule_name
        current_node.children = []

        for seq in result:
            child = ProofNode(sequent=seq)
            current_node.children.append(child)
            stack.append(child)

    return root

r = Prop("r")

G = Sequent(
    relations=[Preorder(x, x)],
    formulas=[LFormula(x, Or(And(p, q), r), Polarity.IN)]
)

tree = saturation_tree(G)

latex = export_proof_to_latex_document(tree)
with open("sat.tex", "w") as f:
    f.write(latex)
