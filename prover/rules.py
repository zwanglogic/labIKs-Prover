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

def rule_and_in(G : Sequent) -> list[Sequent]:
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = And(left,right), polarity = Polarity.IN):
                lst = [] 
                for g in G.formulas:
                        lst.append(g)

                a = LFormula(l,left, Polarity.IN)
                b = LFormula(l,right, Polarity.IN)
                if a not in lst and b not in lst:
                    lst.append(a)
                    lst.append(b)
                seq = Sequent(G.relations,lst)
                return [seq]
    return []

RULES = [
    rule_id,
    rule_bot_in,
    rule_and_in
]

def apply_rules(G : Sequent) -> list[Sequent]:
    for rule in RULES:
        x = rule(G) # x is the resulf of application of the rule

        if x: 
            return x # successfully apply
        
    return [] # no rule can be applied
    
# test 
x = Label("x")
p = Prop("p")
q = Prop("q")
phi = And(p,q)

G = Sequent([], [
    LFormula(x, phi, Polarity.IN),
    
])

print("conclusion:", G)
print("premise:", apply_rules(G))