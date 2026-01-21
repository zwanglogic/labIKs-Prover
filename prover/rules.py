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
                return [Sequent(G.relations, list(new_forms))]
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
                return [Sequent(G.relations, list(new_forms))]
    return None


def rule_and_out(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=And(left, right), polarity=Polarity.OUT):
                a = LFormula(l, left, Polarity.OUT)
                b = LFormula(l, right, Polarity.OUT)
                
                if a in G.formulas or b in G.formulas:
                    continue

                s1 = set(G.formulas); s1.add(a)
                s2 = set(G.formulas); s2.add(b)
                return [Sequent(G.relations, list(s1)), Sequent(G.relations, list(s2))]
    return None


def rule_or_in(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=Or(left, right), polarity=Polarity.IN):
                a = LFormula(l, left, Polarity.IN)
                b = LFormula(l, right, Polarity.IN)
                
                if a in G.formulas or b in G.formulas:
                    continue

                s1 = set(G.formulas); s1.add(a)
                s2 = set(G.formulas); s2.add(b)
                return [Sequent(G.relations, list(s1)), Sequent(G.relations, list(s2))]
    return None


def rule_imp_in(G: Sequent) -> list[Sequent] | None:
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=Imp(left, right), polarity=Polarity.IN):
                a = LFormula(l, left, Polarity.OUT)
                b = LFormula(l, right, Polarity.IN)
                
                if a in G.formulas or b in G.formulas:
                    continue

                s1 = set(G.formulas); s1.add(a)
                s2 = set(G.formulas); s2.add(b)
                return [Sequent(G.relations, list(s1)), Sequent(G.relations, list(s2))]
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
    changes the sequent, or closes the branch.
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

        # Otherwise: rule fired but changed nothing，ignore it

    # No rule produced any progress
    return None
    
