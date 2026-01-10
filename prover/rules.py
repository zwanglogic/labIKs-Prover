from syntax import *

# each rule is a fuction of type Sequent -> list[Sequent]

def rule_id(G : Sequent) -> list[Sequent]:
    for f1 in G.formulas:
        match f1:
            case LFormula(label = l1, formula = Prop(p1), polarity = Polarity.IN):
                for f2 in G.formulas:
                    match f2:
                        case LFormula(label = l2, formula = Prop(p2), polarity = Polarity.OUT) if l1 == l2 and p1 == p2:
                            return []
    return []



RULES = [
    rule_id,
]

def apply_rules(G : Sequent) -> list[Sequent]:
    for rule in RULES:
        x = rule(G) # x is the resulf of application of the rule

        if x: 
            return x # successfully apply
        
    return [] # no rule can be applied
    
# test rule_id
x = Label("x")
A = Prop("A")

G = Sequent([], [
    LFormula(x, A, Polarity.IN),
    LFormula(x, A, Polarity.OUT)
])

print("conclusion:", G)
print("premise:", apply_rules(G))