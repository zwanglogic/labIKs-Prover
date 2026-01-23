from syntax import *


# Given a sequent, for each label appears in it, adding reflexivity relation
def reflexivity(G: Sequent) -> Sequent:
    rels = set(G.relations)
    for x in all_labels(G):
        rels.add(Preorder(x, x))
    if rels == set(G.relations):
        return G  # small optimization: reduce unnecessary object creation

    # print(f"apply_ref: {Sequent(frozenset(rels), G.modal_relations, G.formulas)}")
    return Sequent(frozenset(rels), G.modal_relations, G.formulas)


# Transitive closure
def transitivity(G: Sequent) -> Sequent:
    rels = set(G.relations)
    added = True

    while added:
        added = False
        current = list(rels)
        for r1 in current:
            for r2 in current:
                if r1.right == r2.left:
                    r3 = Preorder(r1.left, r2.right)
                    if r3 not in rels:
                        rels.add(r3)
                        added = True

    if rels == set(G.relations):
        return G
    # print(f"apply trans: {Sequent(frozenset(rels), G.modal_relations, G.formulas)}")
    return Sequent(frozenset(rels), G.modal_relations, G.formulas)


def monotonicity(G: Sequent) -> Sequent:
    rels = set(G.relations)
    forms = set(G.formulas)

    added = True
    while added:
        added = False
        current_forms = list(forms)
        current_rels = list(rels)

        for r in current_rels:
            for f in current_forms:
                if f.label == r.left and f.polarity == Polarity.IN:
                    lifted = LFormula(r.right, f.formula, Polarity.IN)
                    if lifted not in forms:
                        forms.add(lifted)
                        added = True

    if forms == set(G.formulas):
        return G
    # print(f"apply mon: {Sequent(G.relations, G.modal_relations, frozenset(forms))}")
    return Sequent(G.relations, G.modal_relations, frozenset(forms))


# Generate a new label from a list. NOT confused with new_label().
def new_label_list(lst: list) -> Label:
    i = 0
    while True:
        name = f"x{i}"
        lab = Label(name)
        if lab not in lst:
            return lab
        i += 1


def forward_confluence(G: Sequent) -> Sequent:
    rel = set(G.relations)
    m_rel = set(G.modal_relations)

    changed = True
    while changed:
        changed = False
        labels = all_labels(
            Sequent(frozenset(rel), frozenset(m_rel), G.formulas))

        for r1 in list(rel):    # x <= z
            for r2 in list(m_rel):  # x R y
                if r1.left != r2.left:
                    continue

                # check if the witness already exists
                for l in labels:
                    if Preorder(r2.right, l) in rel and Relation(r1.right, l) in m_rel:
                        break
                else:
                    u = new_label_list(labels)
                    labels.append(u)

                    rel.add(Preorder(r2.right, u))  # y <= u
                    m_rel.add(Relation(r1.right, u))    # z R u

                    rel.add(Preorder(u, u))

                    changed = True

    if rel == set(G.relations) and m_rel == set(G.modal_relations):
        return G
    # print(f"apply fc: {Sequent(frozenset(rel), frozenset(m_rel), G.formulas)}")
    return Sequent(frozenset(rel), frozenset(m_rel), G.formulas)


def backward_confluence(G: Sequent) -> Sequent:
    rel = set(G.relations)
    m_rel = set(G.modal_relations)

    changed = True
    while changed:
        changed = False
        labels = all_labels(
            Sequent(frozenset(rel), frozenset(m_rel), G.formulas))

        for r1 in list(rel):  # y <= z
            for r2 in list(m_rel):  # x R y
                if r2.right != r1.left:
                    continue

                # check if the witness already exists
                for l in labels:
                    if (
                        Preorder(r2.left, l) in rel and
                        Relation(l, r1.right) in m_rel
                    ):
                        break
                else:
                    u = new_label_list(labels)
                    labels.append(u)

                    rel.add(Preorder(r2.left, u))   # x <= u
                    m_rel.add(Relation(u, r1.right))  # u R z

                    rel.add(Preorder(u, u))

                    changed = True

    if rel == set(G.relations) and m_rel == set(G.modal_relations):
        return G
    # print(f"apply bc: {Sequent(frozenset(rel), frozenset(m_rel), G.formulas)}")
    return Sequent(frozenset(rel), frozenset(m_rel), G.formulas)


def closure(G: Sequent) -> Sequent:
    cur = G
    while True:
        nxt = cur
        nxt = reflexivity(nxt)
        nxt = transitivity(nxt)
        nxt = monotonicity(nxt)
        nxt = forward_confluence(nxt)
        nxt = backward_confluence(nxt)

        if nxt == cur:
            return cur

        cur = nxt