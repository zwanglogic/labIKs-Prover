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

x = Label("x")

p = Prop("p")
q = Prop("q")
r = Prop("r")

phi = Imp(Or(And(p, q), r), p)

G = Sequent(
    relations=[],
    formulas=[
        LFormula(x, phi, Polarity.IN),
        LFormula(x, p, Polarity.OUT)   
    ]
)

print("Initial:")
print(G)

saturation(G)

x = Label("x")
p = Prop("p")
q = Prop("q")

G = Sequent([], [LFormula(x, And(p, q), Polarity.OUT)])
print("almost happy?", is_almost_happy_sequent(closure(G)))
print("saturation leaves:", saturation(G))


