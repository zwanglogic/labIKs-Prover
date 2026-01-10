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

def rule_bot_in(G : Sequent) -> list[Sequent]:
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = Bot(), polarity = Polarity.IN):
                return []
    return []

RULES = [
    rule_id,
    rule_bot_in
]

def apply_rules(G : Sequent) -> list[Sequent]:
    for rule in RULES:
        x = rule(G) # x is the resulf of application of the rule

        if x: 
            return x # successfully apply
        
    return [] # no rule can be applied
    
# test 
x = Label("x")
A = Bot()

G = Sequent([], [
    LFormula(x, A, Polarity.IN),
    
])

print("conclusion:", G)
print("premise:", apply_rules(G))