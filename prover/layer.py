from syntax import *
from happy import *

import itertools
from typing import Dict, Iterable, Set  # For bijection generator


def symmetric_closure(G: Sequent) -> set[tuple[Label, Label]]:
    """
    Definition 5.1: Compute R_G union R_G^{-1}.
    """
    rel = set()
    for r in G.modal_relations:
        rel.add((r.left, r.right))
        rel.add((r.right, r.left))
    return rel


def reflexive_transitive_closure(base: set[tuple[Label, Label]], labels: set[Label]) -> set[tuple[Label, Label]]:
    """
    Compute the reflexive and transitive closure of a binary relation.

    Potential problem: O(n^3), very slow.
    """
    c = set(base)

    # reflexivity
    for x in labels:
        c.add((x, x))

    # transitivity
    changed = True
    while changed:
        changed = False
        current = list(c)
        for (x, y) in current:
            for (y2, z) in current:
                if y == y2 and (x, z) not in c:
                    c.add((x, z))
                    changed = True

    return c


def compute_equiv_relation(G: Sequent) -> set[tuple[Label, Label]]:
    """
    Given two labels in G, compute the equivalence relation in definition 5.1.

    x equiv y  iff  (x, y) in closure(R_G union R_G^{-1})^*

    Idea: computing the reflexive transitive closure is pretty expensive,
    so instead of recomputing it everywhere,
    we now compute it once and pass it around to the functions that need it.
    """
    labels = set(all_labels(G))
    base = symmetric_closure(G)
    return reflexive_transitive_closure(base, labels)


def are_equivalent_from_closure(c: set[tuple[Label, Label]], x: Label, y: Label) -> bool:
    """
    Given two labels in G, determine whether they are equivalent under the relation in definition 5.1.
    """
    return (x, y) in c


def layer(G: Sequent, c: set[tuple[Label, Label]], x: Label) -> set[Label]:
    """
    Definition 5.1 (Layer)

    Compute the equivalence class of a label 'x' under the relation 'c'.
    """
    equiv_class = set()
    for y in all_labels(G):
        if are_equivalent_from_closure(c, x, y):
            if y not in equiv_class:
                equiv_class.add(y)

    return equiv_class


def all_layers(G: Sequent, c: set[tuple[Label, Label]]) -> list[set[Label]]:
    """
    Compute all layers in G under relation 'c'.
    """
    layers = []
    for x in all_labels(G):
        l = layer(G, c, x)
        if l not in layers:
            layers.append(l)

    return layers


def is_layered(G: Sequent, c: set[tuple[Label, Label]]):
    """
    Definition 5.2 (Layered sequent)

    Determine whether a sequent G is layered under relation 'c'.

    Potential problem: the complexity is O(n^4) :(
    """
    labels = all_labels(G)

    # Condition 1
    for x in labels:
        for y in labels:
            if x != y:
                if are_equivalent_from_closure(c, x, y):
                    if Preorder(x, y) in G.relations or Preorder(y, x) in G.relations:
                        return False
    # Condition 2
    for x in labels:
        for y in labels:
            for s in labels:
                for t in labels:
                    if x != s:
                        if (
                            are_equivalent_from_closure(c, x, y)
                            and are_equivalent_from_closure(c, s, t)
                            and Preorder(x, s) in G.relations
                        ):
                            if Preorder(t, y) in G.relations:
                                return False
    return True


def order_layer(G: Sequent, L1: set[Label], L2: set[Label]) -> bool:
    """
    Determine whether L1 < L2.
    """
    if L1 == L2:
        return False

    for x in L1:
        for y in L2:
            if Preorder(x, y) in G.relations:
                return True
    return False


def is_happy_layer(G: Sequent, L: set[Label]) -> bool:
    """
    Definition 5.1

    A layer L is happy if all labels in L are happy.
    """
    for x in L:
        if not is_happy_label(G, x):
            return False
    return True


def all_bijections(L1: Set[Label], L2: Set[Label]) -> Iterable[Dict[Label, Label]]:
    """
    Generate all bijections f : L1 -> L2.

    Potential problem: the complexity is O(n!). Terrible.
    """
    if len(L1) != len(L2):
        return  # no bijection exists

    L1_list = list(L1)
    L2_list = list(L2)

    for perm in itertools.permutations(L2_list):
        # We don't need to compute all bijections.
        yield dict(zip(L1_list, perm))

def contain_same_formulas(G: Sequent, x: Label, y: Label) -> bool:
    """
    Determine whether the components (formula, polarity) under x, y are the same.
    """
    x_formulas = set()
    y_formulas = set()
    
    for f in G.formulas:
        if f.label == x:
            x_formulas.add((f.formula, f.polarity)) 
        elif f.label == y:
            y_formulas.add((f.formula, f.polarity))
            
    return x_formulas == y_formulas



def are_equivalent_layers(G: Sequent, L1: set[Label], L2: set[Label], c: set[tuple[Label, Label]]) -> bool:
    """
    Definition 5.14 (Equivalent layers)
    """
    if len(L1) != len(L2):
        return False

    for f in all_bijections(L1, L2):
        flag1 = True
        flag2 = True
        for x in L1:
            for y in L1:
                if not contain_same_formulas(G, x, f[x]):
                    flag1 = False
                lhs = Relation(x, y) in G.modal_relations
                rhs = Relation(f[x], f[y]) in G.modal_relations
                if not (lhs == rhs):
                    flag2 = False

        if flag1 and flag2:
            return True
    return False


def is_allowed_formula(G: Sequent, f: LFormula, c: set[tuple[Label, Label]]) -> bool:
    """
    Definition 5.15 (Allowed formula)
    """
    assert f in G.formulas, f"{f} is not in {G}"

    match f:
        case LFormula(_, Imp(_, _), Polarity.OUT):
            pass
        case LFormula(_, Box(_), Polarity.OUT):
            pass
        case _:
            return False

    x = f.label
    L = layer(G, c, x)

    for Lp in all_layers(G, c):
        if not order_layer(G, Lp, L):
            continue

        if are_equivalent_layers(G, Lp, L, c):
            return False

        if not is_happy_layer(G, Lp):
            return False

    return True