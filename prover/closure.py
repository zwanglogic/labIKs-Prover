from syntax import *

# Given a sequent, for each label appears in it, adding reflexivity relation
def reflexivity(G : Sequent):
    lst = all_labels(G)

    for x in lst:
        rel = Preorder(x,x)
        if rel not in G.relations:
            G.relations.append(rel)
            flag = True
    
# transitive closure
def transitivity(G: Sequent):
    changed = False
    rel = G.relations.copy()

    for r1 in rel:
        for r2 in rel:
            if r1.right == r2.left:
                r3 = Preorder(r1.left, r2.right)
                if r3 not in G.relations:
                    G.relations.append(r3)
                    changed = True

    if changed:
        transitivity(G)


def monotonicity(G: Sequent):
    changed = False
    rel = G.relations.copy()
    formulas = G.formulas.copy()

    for r in rel:
        for f in formulas:
            if f.label == r.left and f.polarity == Polarity.IN:
                form = LFormula(r.right, f.formula, Polarity.IN)
                if form not in G.formulas:
                    G.formulas.append(form)
                    changed = True

    if changed:
        monotonicity(G)


# reflexive transitive monotonicity closure
def closure(G: Sequent) -> Sequent:
    newG = Sequent(G.relations.copy(), G.formulas.copy())

    old_state = None
    while old_state != (len(newG.relations), len(newG.formulas)):
        old_state = (len(newG.relations), len(newG.formulas))
        reflexivity(newG)
        transitivity(newG)
        monotonicity(newG)

    return newG

