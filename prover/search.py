from rules import *
from closure import *
from syntax import *

# if the sequent is initial
def is_closed(G : Sequent) -> bool:
    # bot
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = Bot(), polarity = Polarity.IN):
                return True
            
    # id
    for f1 in G.formulas:
        match f1:
            case LFormula(label = l1, formula = Prop(p1), polarity = Polarity.IN):
                for f2 in G.formulas:
                    match f2:
                        case LFormula(label = l2, formula = Prop(p2), polarity = Polarity.OUT) if l1 == l2 and p1 == p2:
                            return True

    return False

# a naive search algorithm. might not terminate.
def dfs_search(G : Sequent) -> bool:
    G = closure(G)

    if is_closed(G):
        return True
    
    for premises in apply_rules(G):
        if dfs_search(premises):
            return True
    return False

