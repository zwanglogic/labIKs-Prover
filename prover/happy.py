from syntax import *
from closure import *

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

def is_happy_label(G: Sequent, x: Label) -> bool:
    for f in G.formulas:
        if f.label == x:
            if not is_happy_formula(G, f):
                return False
    return True

def is_happy_sequent(G: Sequent) -> bool:
    G_closed = closure(G)

    # structural happiness
    if set(G_closed.relations) != set(G.relations):
        return False
    if set(G_closed.formulas) != set(G.formulas):
        return False

    for l in all_labels(G):
        if not is_happy_label(G, l):
            return False

    return True


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

x = Label("x")
y = Label("y")
A = Prop("A")

G = Sequent(
    relations=[
        Preorder(x, y)
    ],
    formulas=[
        LFormula(x, A, Polarity.IN)
    ]
)


print(is_happy_sequent(G)) 