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
        current_seq = lst.pop()
        outcome = apply_one_rule(current_seq, saturation_rules)

        if outcome == None:
            leaves.append(current_seq)
        else:
            lst.extend(outcome)

    return leaves

