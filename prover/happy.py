from syntax import *
from closure import *


def is_happy_formula(G: Sequent, f: LFormula) -> bool:
    """
    Definition 4.3 (Happy labelled formula)
    """
    if f not in G.formulas:
        raise ValueError("formula not in sequent")

    match f:
        # x: a in is always happy
        case LFormula(label=x, formula=Prop(p), polarity=Polarity.IN):
            return True

        # x: bot out is always happy
        case LFormula(label=x, formula=Bot(), polarity=Polarity.OUT):
            return True

        # x: bot in is never happy
        case LFormula(label=x, formula=Bot(), polarity=Polarity.IN):
            return False

        # x: a out is happy iff x: a in not in G
        case LFormula(label=x, formula=Prop(p), polarity=Polarity.OUT):
            if LFormula(x, Prop(p), Polarity.IN) not in G.formulas:
                return True
            else:
                return False

        # x: A and B in
        case LFormula(label=x, formula=And(A, B), polarity=Polarity.IN):
            if LFormula(x, A, Polarity.IN) in G.formulas and LFormula(x, B, Polarity.IN) in G.formulas:
                return True
            else:
                return False

        # x: A and B out
        case LFormula(label=x, formula=And(A, B), polarity=Polarity.OUT):
            if LFormula(x, A, Polarity.OUT) in G.formulas or LFormula(x, B, Polarity.OUT) in G.formulas:
                return True
            else:
                return False

        # x: A or B in
        case LFormula(label=x, formula=Or(A, B), polarity=Polarity.IN):
            if LFormula(x, A, Polarity.IN) in G.formulas or LFormula(x, B, Polarity.IN) in G.formulas:
                return True
            else:
                return False

        # x: A or B out
        case LFormula(label=x, formula=Or(A, B), polarity=Polarity.OUT):
            if LFormula(x, A, Polarity.OUT) in G.formulas and LFormula(x, B, Polarity.OUT) in G.formulas:
                return True
            else:
                return False

        # x: A to B in
        case LFormula(label=x, formula=Imp(A, B), polarity=Polarity.IN):
            if LFormula(x, A, Polarity.OUT) in G.formulas or LFormula(x, B, Polarity.IN) in G.formulas:
                return True
            else:
                return False

        # x: A to B out
        case LFormula(label=x, formula=Imp(A, B), polarity=Polarity.OUT):
            for y in all_labels(G):
                if LFormula(y, A, Polarity.IN) in G.formulas and LFormula(y, B, Polarity.OUT) in G.formulas and Preorder(x, y) in G.relations:
                    return True
            else:
                return False

        # x: Box A in
        case LFormula(label=x, formula=Box(A), polarity=Polarity.IN):
            for z in all_labels(G):
                if Relation(x, z) in G.modal_relations:
                    if LFormula(z, A, Polarity.IN) not in G.formulas:
                        return False
            return True

        # x: Box A out
        case LFormula(label=x, formula=Box(A), polarity=Polarity.OUT):
            for z in all_labels(G):
                for y in all_labels(G):
                    if Preorder(x, y) in G.relations and Relation(y, z) in G.modal_relations:
                        if LFormula(z, A, Polarity.OUT) in G.formulas:
                            return True
            return False

        # x: Diamond A in
        case LFormula(label=x, formula=Diamond(A), polarity=Polarity.IN):
            for z in all_labels(G):
                if Relation(x, z) in G.modal_relations:
                    if LFormula(z, A, Polarity.IN) in G.formulas:
                        return True
            return False

        # x: Diamond A out
        case LFormula(label=x, formula=Diamond(A), polarity=Polarity.OUT):
            for y in all_labels(G):
                if Relation(x, y) in G.modal_relations:
                    if LFormula(y, A, Polarity.OUT) not in G.formulas:
                        return False
            return True

    raise NotImplementedError


def is_happy_label(G: Sequent, x: Label) -> bool:
    """
    Definition 4.4 (Happy label)
    """
    for f in G.formulas:
        if f.label == x:
            if not is_happy_formula(G, f):
                return False

    return True


def is_structurally_happy(G: Sequent) -> bool:
    """
    Definition 4.5 (Structurally happy sequent)
    """
    return closure(G) == G


def is_happy_sequent(G: Sequent) -> bool:
    """
    Definition 4.6 (Happy sequent)
    """
    if not is_structurally_happy(G):
        return False

    for l in all_labels(G):
        if not is_happy_label(G, l):
            return False

    return True


def is_almost_happy_label(G: Sequent, x: Label) -> bool:
    """
    Definition 5.4 (Almost happy label)
    """
    for f in G.formulas:
        if f.label != x:
            continue

        match f:
            case LFormula(_, Bot(), Polarity.IN):
                continue
            case LFormula(_, Prop(_), Polarity.OUT):
                continue
            case LFormula(_, Imp(_, _), Polarity.OUT):
                continue
            case LFormula(_, Box(_), Polarity.OUT):
                continue

        if not is_happy_formula(G, f):
            return False

    return True


def is_almost_happy_sequent(G: Sequent) -> bool:
    """
    Definition 5.4 (Almost happy sequent)
    """
    for l in all_labels(G):
        if not is_almost_happy_label(G, l):
            return False

    return True