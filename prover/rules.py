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

def rule_or_out(G : Sequent) -> list[Sequent]:
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = Or(left,right), polarity = Polarity.OUT):
                lst = [] 
                for g in G.formulas:
                        lst.append(g)

                a = LFormula(l,left, Polarity.OUT)
                b = LFormula(l,right, Polarity.OUT)
                if a not in lst and b not in lst:
                    lst.append(a)
                    lst.append(b)
                seq = Sequent(G.relations,lst)
                return [seq]
    return []

def rule_and_out(G : Sequent) -> list[Sequent]:
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = And(left, right), polarity = Polarity.OUT):
                lst1 = []

                for g in G.formulas:
                        lst1.append(g)

                a = LFormula(l,left, Polarity.OUT)
                if a not in lst1:
                    lst1.append(a)
                seq1 = Sequent(G.relations,lst1)

                lst2 = []
                for g in G.formulas:
                        lst2.append(g)

                b = LFormula(l,right, Polarity.OUT)
                if b not in lst2:
                    lst2.append(b)
                seq2 = Sequent(G.relations,lst2)

                return [seq1,seq2]
    return []        

def rule_or_in(G : Sequent) -> list[Sequent]:
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = Or(left, right), polarity = Polarity.IN):
                lst1 = []

                for g in G.formulas:
                        lst1.append(g)

                a = LFormula(l,left, Polarity.IN)
                if a not in lst1:
                    lst1.append(a)
                seq1 = Sequent(G.relations,lst1)

                lst2 = []
                for g in G.formulas:
                        lst2.append(g)

                b = LFormula(l,right, Polarity.IN)
                if b not in lst2:
                    lst2.append(b)
                seq2 = Sequent(G.relations,lst2)

                return [seq1,seq2]
    return []      

def rule_imp_in(G : Sequent) -> list[Sequent]:
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = Imp(left, right), polarity = Polarity.IN):
                lst1 = []

                for g in G.formulas:
                        lst1.append(g)

                a = LFormula(l,left, Polarity.OUT)
                if a not in lst1:
                    lst1.append(a)
                seq1 = Sequent(G.relations,lst1)

                lst2 = []
                for g in G.formulas:
                        lst2.append(g)

                b = LFormula(l,right, Polarity.IN)
                if b not in lst2:
                    lst2.append(b)
                seq2 = Sequent(G.relations,lst2)

                return [seq1,seq2]
    return []    

def rule_imp_out(G : Sequent) -> list[Sequent]:
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = Imp(left,right), polarity = Polarity.OUT):
                lst = [] 
                for g in G.formulas:
                        lst.append(g)

                new_lab = new_label(G)
                new_rel = Preorder(l,new_lab)

                lst2 = [] 
                for r in G.relations:
                        lst2.append(r)
                lst2.append(new_rel)
                
                a = LFormula(new_lab,left, Polarity.IN)
                b = LFormula(new_lab,right, Polarity.OUT)
                if a not in lst and b not in lst:
                    lst.append(a)
                    lst.append(b)
                seq = Sequent(lst2,lst)
                return [seq]
    return []  

RULES = [
    rule_id,
    rule_bot_in,
    rule_and_in,
    rule_or_out,
    rule_and_out,
    rule_or_in,
    rule_imp_in,
    rule_imp_out
]

def apply_rules(G : Sequent) -> list[Sequent]:
    for rule in RULES:
        x = rule(G) # x is the resulf of application of the rule

        if x: 
            return x # successfully apply
        
    return [] # no rule can be applied

def print_premises(premises: list[Sequent]):
    i = 1
    for seq in premises:
        print(f"premise {i}: {seq}")
        i += 1

    
# test 
x = Label("x")
p = Prop("p")
q = Prop("q")
phi = Or(p,q)

G = Sequent([], [
    LFormula(x, phi, Polarity.IN),
    
])

print("conclusion:", G)

x = apply_rules(G)

print_premises(x)