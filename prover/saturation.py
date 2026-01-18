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

# labels
x = Label("x")

# formulas
p = Prop("p")
q = Prop("q")

# initial sequent
G = Sequent(
    relations=[],
    formulas=[
        LFormula(x, Or(p, q), Polarity.IN)
    ]
)

leaves = saturation(G)

print("Leaves:")
for L in leaves:
    print(L)
        
    