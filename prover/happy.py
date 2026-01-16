from syntax import *

def is_happy_formula(G: Sequent, f : LFormula) -> bool:
    if f not in G.formulas:
        raise ValueError("formula not in sequent")
    match f:
        # x: a in is always happy
        case LFormula(label = x, formula = Prop(p), polarity = Polarity.IN): 
            return True
        # x: bot out is always happy
        case LFormula(label = x, formula = Bot(), polarity = Polarity.OUT): 
            return True
        # x: bot in is never happy
        case LFormula(label = x, formula = Bot(), polarity = Polarity.IN): 
            return False
        # x: a out is happy iff x: a in not in G
        case LFormula(label = x, formula = Prop(p), polarity = Polarity.OUT): 
            if LFormula(x, Prop(p), Polarity.IN) not in G.formulas:
                return True
            else: 
                return False
        # x: A and B in
        case LFormula(label = x, formula = And(A,B), polarity = Polarity.IN): 
            if LFormula(x, A, Polarity.IN) in G.formulas and LFormula(x, B, Polarity.IN) in G.formulas:
                return True
            else: 
                return False
        # x: A and B out
        case LFormula(label = x, formula = And(A,B), polarity = Polarity.OUT): 
            if LFormula(x, A, Polarity.OUT) in G.formulas or LFormula(x, B, Polarity.OUT) in G.formulas:
                return True
            else: 
                return False
        # x: A or B in
        case LFormula(label = x, formula = Or(A,B), polarity = Polarity.IN): 
            if LFormula(x, A, Polarity.IN) in G.formulas or LFormula(x, B, Polarity.IN) in G.formulas:
                return True
            else: 
                return False
        # x: A or B out
        case LFormula(label = x, formula = Or(A,B), polarity = Polarity.OUT): 
            if LFormula(x, A, Polarity.OUT) in G.formulas and LFormula(x, B, Polarity.OUT) in G.formulas:
                return True
            else: 
                return False
        # x: A to B in
        case LFormula(label = x, formula = Imp(A,B), polarity = Polarity.IN): 
            if LFormula(x, A, Polarity.OUT) in G.formulas or LFormula(x, B, Polarity.IN) in G.formulas:
                return True
            else: 
                return False
        # x: A to B out
        case LFormula(label = x, formula = Imp(A,B), polarity = Polarity.OUT):
            for y in all_labels(G):
                if LFormula(y, A, Polarity.IN) in G.formulas and LFormula(y, B, Polarity.OUT) in G.formulas and Preorder(x,y) in G.relations:
                    return True
            else:
                    return False
    raise NotImplementedError


# test
x = Label("x")
y = Label("y")
A = Prop("A")
B = Prop("B")

G = Sequent(
    relations=[Preorder(x, y)],
    formulas=[
        LFormula(x, Imp(A,B), Polarity.OUT),
        LFormula(y, A, Polarity.IN),
        LFormula(y, B, Polarity.OUT),
    ]
)

print(is_happy_formula(G, LFormula(x, Imp(A,B), Polarity.OUT)))