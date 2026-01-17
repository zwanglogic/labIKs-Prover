from syntax import *
from happy import *
from closure import *
from rules import *

saturation_rules = [
    rule_and_in,
    rule_and_out,
    rule_or_in,
    rule_or_out,
    rule_imp_in
]

# consider the saturation as computing the fixpoint
def saturation(G : Sequent) -> list[Sequent]:
    G = closure(G)

    lst = [G.copy()]
    leaves =[]

    while lst:
        current_seq = lst.pop() # DFS
        outcome = apply_one_rule(current_seq, saturation_rules)

        if outcome == None:
            leaves.append(current_seq)
        else:
            lst.extend(outcome)

    return leaves

# test
x = Label("x")

P = Prop("P")
Q = Prop("Q")

phi = Imp(Or(P, Q), P)

G0 = Sequent(
    relations = [],
    formulas = [
        LFormula(x, phi, Polarity.OUT)
    ]
)

print("Initial goal:")
print(G0)

leaves = saturation(G0)

print("\nNumber of saturated leaves:", len(leaves))

for i, L in enumerate(leaves):
    print(f"\nLeaf {i}:")
    print(L)
    