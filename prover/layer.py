from syntax import *
from happy import *


# Without modality, all_layers(G) = [{x} | x is label appearing in G}]
def all_layers(G : Sequent):
    return [{x} for x in all_labels(G)]

def is_layered(G : Sequent):
    labels = all_labels(G)

    # Condition 1 is vacuously true in IPL
    # Condition 2 is simply the antisymmetric condition

    for x in labels:
        for y in labels:
            if x == y:
                continue
            if (
                Preorder(x, y) in G.relations and
                Preorder(y, x) in G.relations
            ):
                return False

    return True


# order_layer({x}, {y}) iff Preorder(x, y)

def order_layer(G: Sequent, L1: set[Label], L2: set[Label]) -> bool:
    assert len(L1) == 1 and len(L2) == 1
    x = next(iter(L1))
    y = next(iter(L2))
    return Preorder(x, y) in G.relations


def is_happy_layer(G: Sequent, L: set[Label]) -> bool:
    x = next(iter(L))
    Gc = closure(G)
    for f in Gc.formulas:
        if f.label == x and not is_happy_formula(Gc, f):
            return False
    return True


def are_equivalent_layers(G: Sequent, L1: set[Label], L2: set[Label]) -> bool:
    x = next(iter(L1))
    y = next(iter(L2))
    Gc = closure(G)

    content_x = {(f.formula, f.polarity) for f in Gc.formulas if f.label == x}
    content_y = {(f.formula, f.polarity) for f in Gc.formulas if f.label == y}
    return content_x == content_y


def is_allowed_formula(G: Sequent, f: LFormula) -> bool:
    assert f in G.formulas, f"{f} is not in {G}"

    match f:
        case LFormula(_, Imp(_, _), Polarity.OUT):
            pass
        case _:
            return False

    Gc = closure(G)

    if is_happy_formula(Gc, f):
        return False

    current = {f.label}
    for Lp in all_layers(Gc):
        if Lp == current:
            continue

        # strict lower: Lp < current  (more robust than relying on is_layered)
        if order_layer(Gc, Lp, current) and not order_layer(Gc, current, Lp):
            if not is_happy_layer(Gc, Lp):
                return False
            if are_equivalent_layers(Gc, Lp, current):
                return False

    return True