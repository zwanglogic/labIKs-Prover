from syntax import *
from closure import *
from prooftree import *
from happy import *

# each rule is a fuction of type Sequent -> list[Sequent] or None

def rule_id(G: Sequent):
    for f1 in G.formulas:
        match f1:
            case LFormula(l1, Prop(p1), Polarity.IN):
                for f2 in G.formulas:
                    match f2:
                        case LFormula(l2, Prop(p2), Polarity.OUT) if l1 == l2 and p1 == p2:
                            return []  # close branch
    return None

def rule_bot_in(G: Sequent):
    for f in G.formulas:
        if isinstance(f.formula, Bot) and f.polarity == Polarity.IN:
            return []
    return None

def rule_and_in(G: Sequent):
    for f in G.formulas:
        match f:
            case LFormula(l, And(A, B), Polarity.IN):
                a = LFormula(l, A, Polarity.IN)
                b = LFormula(l, B, Polarity.IN)

                if a in G.formulas and b in G.formulas:
                    return None   

                new_forms = set(G.formulas)
                new_forms.add(a)
                new_forms.add(b)

                return [Sequent(G.relations, list(new_forms))]
    return None
def rule_or_out(G: Sequent):
    for f in G.formulas:
        match f:
            case LFormula(l, Or(A, B), Polarity.OUT):
                a = LFormula(l, A, Polarity.OUT)
                b = LFormula(l, B, Polarity.OUT)

                if a in G.formulas and b in G.formulas:
                    return None

                new_forms = set(G.formulas)
                new_forms.add(a)
                new_forms.add(b)

                return [Sequent(G.relations, list(new_forms))]
    return None

def rule_and_out(G: Sequent):
    for f in G.formulas:
        match f:
            case LFormula(l, And(A, B), Polarity.OUT):
                a = LFormula(l, A, Polarity.OUT)
                b = LFormula(l, B, Polarity.OUT)

                if a in G.formulas or b in G.formulas:
                    return None

                s1 = set(G.formulas); s1.add(a)
                s2 = set(G.formulas); s2.add(b)

                return [
                    Sequent(G.relations, list(s1)),
                    Sequent(G.relations, list(s2)),
                ]
    return None

def rule_or_in(G: Sequent):
    for f in G.formulas:
        match f:
            case LFormula(l, Or(left, right), Polarity.IN):
                a = LFormula(l, left, Polarity.IN)
                b = LFormula(l, right, Polarity.IN)

                if a in G.formulas or b in G.formulas:
                    return None

                s1 = set(G.formulas)
                s1.add(a)

                s2 = set(G.formulas)
                s2.add(b)

                return [
                    Sequent(G.relations, list(s1)),
                    Sequent(G.relations, list(s2))
                ]
    return None

def rule_imp_in(G: Sequent):
    for f in G.formulas:
        match f:
            case LFormula(l, Imp(A, B), Polarity.IN):
                a = LFormula(l, A, Polarity.OUT)
                b = LFormula(l, B, Polarity.IN)

                if a in G.formulas or b in G.formulas:
                    return None

                s1 = set(G.formulas)
                s1.add(a)

                s2 = set(G.formulas)
                s2.add(b)

                return [
                    Sequent(G.relations, list(s1)),
                    Sequent(G.relations, list(s2))
                ]
    return None  

def rule_imp_out(G: Sequent):
    for f in G.formulas:
        match f:
            case LFormula(x, Imp(A, B), Polarity.OUT):

                for y in all_labels(G):
                    if (
                        Preorder(x, y) in G.relations and
                        LFormula(y, A, Polarity.IN) in G.formulas and
                        LFormula(y, B, Polarity.OUT) in G.formulas
                    ):
                        return None   

                y = new_label(G)

                new_rels = set(G.relations)
                new_rels.add(Preorder(x, y))
                new_rels.add(Preorder(y, y))  

                new_forms = set(G.formulas)
                new_forms.add(LFormula(y, A, Polarity.IN))
                new_forms.add(LFormula(y, B, Polarity.OUT))

                return [Sequent(list(new_rels), list(new_forms))]
    return None

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


"""
Try to apply one saturation rule to the sequent G.

Notes:
- A rule application is considered valid only if it produces
    new information (i.e. changes the sequent), or closes the branch.
- This function is responsible for rule scheduling and progress control.
 """
def try_apply_rule(G: Sequent, rules: list) -> list[Sequent] | None:

    # Always work on the closure of G
    Gc = closure(G)

    old_forms = set(Gc.formulas)
    old_rels  = set(Gc.relations)

    for rule in rules:
        result = rule(Gc)

        # Rule not applicable
        if result is None:
            continue

        # Branch closed 
        if result == []:
            try_apply_rule.__last_rule_name__ = rule.__name__
            return []

        # Check whether the rule really makes progress
        new_seqs = []
        progressed = False

        for seq in result:
            seq_c = closure(seq)

            if (
                set(seq_c.formulas) != old_forms or
                set(seq_c.relations) != old_rels
            ):
                progressed = True

            new_seqs.append(seq_c)

        # Accept this rule application only if progress is made
        if progressed:
            try_apply_rule.__last_rule_name__ = rule.__name__
            return new_seqs

        # Otherwise: rule fired but changed nothing → ignore it

    # No rule produced any progress
    return None
