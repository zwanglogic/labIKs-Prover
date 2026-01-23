from syntax import *
from closure import *


# Each rule is a fuction of type Sequent -> list[Sequent] or None
def rule_id(G: Sequent) -> list[Sequent] | None:
    for f1 in G.formulas:
        match f1:
            case LFormula(label=l1, formula=Prop(p1), polarity=Polarity.IN):
                for f2 in G.formulas:
                    match f2:
                        case LFormula(label=l2, formula=Prop(p2), polarity=Polarity.OUT):
                            if l1 == l2 and p1 == p2:
                                return []  # Close branch
    return None


def rule_bot_in(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(formula=Bot(), polarity=Polarity.IN):
                return []  # Close branch
    return None


def rule_and_in(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=And(left, right), polarity=Polarity.IN):
                a = LFormula(l, left, Polarity.IN)
                b = LFormula(l, right, Polarity.IN)

                if a in G.formulas and b in G.formulas:
                    continue

                new_forms = set(G.formulas)
                new_forms.add(a)
                new_forms.add(b)
                return [Sequent(G.relations, G.modal_relations, frozenset(new_forms))]
    return None


def rule_or_out(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=Or(left, right), polarity=Polarity.OUT):
                a = LFormula(l, left, Polarity.OUT)
                b = LFormula(l, right, Polarity.OUT)

                if a in G.formulas and b in G.formulas:
                    continue

                new_forms = set(G.formulas)
                new_forms.add(a)
                new_forms.add(b)
                return [Sequent(G.relations, G.modal_relations, frozenset(new_forms))]
    return None


def rule_and_out(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=And(left, right), polarity=Polarity.OUT):
                a = LFormula(l, left, Polarity.OUT)
                b = LFormula(l, right, Polarity.OUT)

                if a in G.formulas or b in G.formulas:
                    continue

                s1 = set(G.formulas)
                s1.add(a)
                s2 = set(G.formulas)
                s2.add(b)
                return [Sequent(G.relations, G.modal_relations, frozenset(s1)), Sequent(G.relations, G.modal_relations, frozenset(s2))]
    return None


def rule_or_in(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=Or(left, right), polarity=Polarity.IN):
                a = LFormula(l, left, Polarity.IN)
                b = LFormula(l, right, Polarity.IN)

                if a in G.formulas or b in G.formulas:
                    continue

                s1 = set(G.formulas)
                s1.add(a)
                s2 = set(G.formulas)
                s2.add(b)
                return [Sequent(G.relations, G.modal_relations, frozenset(s1)), Sequent(G.relations, G.modal_relations, frozenset(s2))]
    return None


def rule_imp_in(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=Imp(left, right), polarity=Polarity.IN):
                a = LFormula(l, left, Polarity.OUT)
                b = LFormula(l, right, Polarity.IN)

                if a in G.formulas or b in G.formulas:
                    continue

                s1 = set(G.formulas)
                s1.add(a)
                s2 = set(G.formulas)
                s2.add(b)
                return [Sequent(G.relations, G.modal_relations, frozenset(s1)), Sequent(G.relations, G.modal_relations, frozenset(s2))]
    return None


def rule_imp_out(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=x, formula=Imp(left, right), polarity=Polarity.OUT):

                already_exists = False
                for y in all_labels(G):
                    if (Preorder(x, y) in G.relations and
                        LFormula(y, left, Polarity.IN) in G.formulas and
                            LFormula(y, right, Polarity.OUT) in G.formulas):
                        already_exists = True
                        break

                if already_exists:
                    continue

                y = new_label(G)
                new_rels = set(G.relations)
                new_rels.add(Preorder(x, y))
                new_rels.add(Preorder(y, y))

                new_forms = set(G.formulas)
                new_forms.add(LFormula(y, left, Polarity.IN))
                new_forms.add(LFormula(y, right, Polarity.OUT))
                return [Sequent(frozenset(new_rels), G.modal_relations, frozenset(new_forms))]
    return None


def rule_box_in(G: Sequent) -> list[Sequent] | None:
    for r in G.modal_relations:
        match r:
            case Relation(left=x, right=y):
                for f in G.formulas:
                    match f:
                        case LFormula(label=l, formula=Box(A), polarity=Polarity.IN) if l == x:
                            a = LFormula(y, A, Polarity.IN)

                            if a in G.formulas:
                                continue

                            s = set(G.formulas)
                            s.add(a)
                            return [Sequent(G.relations, G.modal_relations, frozenset(s))]
    return None


def rule_diamond_out(G: Sequent) -> list[Sequent] | None:
    for r in G.modal_relations:
        match r:
            case Relation(left=x, right=y):
                for f in G.formulas:
                    match f:
                        case LFormula(label=l, formula=Diamond(A), polarity=Polarity.OUT) if l == x:
                            a = LFormula(y, A, Polarity.IN)

                            if a in G.formulas:
                                continue

                            s = set(G.formulas)
                            s.add(a)
                            return [Sequent(G.relations, G.modal_relations, frozenset(s))]
    return None


def rule_diamond_in(G: Sequent) -> list[Sequent] | None:
    y = new_label(G)

    for f in G.formulas:
        match f:
            case LFormula(label=x, formula=Diamond(A), polarity=Polarity.IN):
                a = LFormula(y, A, Polarity.IN)
                r = Relation(x, y)

                new_form = set(G.formulas)
                new_form.add(a)
                new_rel = set(G.modal_relations)
                new_rel.add(r)

                return [Sequent(G.relations, frozenset(new_rel), frozenset(new_form))]

    return None


def rule_box_out(G: Sequent) -> list[Sequent] | None:
    u, z = fresh_labels(G, 2)

    for f in G.formulas:
        match f:
            case LFormula(label=x, formula=Box(A), polarity=Polarity.OUT):
                a = LFormula(z, A, Polarity.OUT)
                r = Relation(u, z)
                p = Preorder(x, u)

                new_form = set(G.formulas)
                new_form.add(a)
                new_m_rel = set(G.modal_relations)
                new_m_rel.add(r)
                new_rel = set(G.relations)
                new_rel.add(p)

                return [Sequent(frozenset(new_rel), frozenset(new_m_rel), frozenset(new_form))]

    return None


RULES = [
    rule_id,
    rule_bot_in,
    rule_and_in,
    rule_or_out,
    rule_and_out,
    rule_or_in,
    rule_imp_in,
    rule_imp_out,
    rule_box_in,
    rule_diamond_out,
    rule_diamond_in,
    rule_box_out
]


def try_apply_rule(G: Sequent, rules: list) -> list[Sequent] | None:
    """
    Try to apply one rule from the list to the sequent G.

    A rule application is valid if it:
    closes the branch, or produces genuine progress on formulas / preorder / modal relations.
    """

    Gc = closure(G)

    old_forms = set(Gc.formulas)
    old_rels = set(Gc.relations)
    old_mrels = set(Gc.modal_relations)

    for rule in rules:
        result = rule(Gc)

        if result is None:
            continue

        # Branch closed
        if result == []:
            try_apply_rule.__last_rule_name__ = rule.__name__
            return []

        new_seqs = []
        progressed = False

        for seq in result:
            seq_c = closure(seq)

            if (
                set(seq_c.formulas) != old_forms or
                set(seq_c.relations) != old_rels or
                set(seq_c.modal_relations) != old_mrels
            ):
                progressed = True

            new_seqs.append(seq_c)

        if progressed:
            try_apply_rule.__last_rule_name__ = rule.__name__
            return new_seqs

    return None