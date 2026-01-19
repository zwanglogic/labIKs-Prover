from syntax import *
from closure import *
from prooftree import *

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

def apply_one_rule(G : Sequent, set_of_rules : list) -> list[Sequent]:
     G = closure(G)
     for rule in set_of_rules:
        result = rule(G)
        if result:      
            print_step(G, rule.__name__, result)   
            return result
     return None
          
def apply_one_rule_node(node: ProofNode, rules: list) -> bool:
    G = node.sequent

    for rule in rules:
        outcome = rule(G)

        if outcome:
            node.rule = rule.__name__

            children = []
            for new_seq in outcome:
                child = ProofNode(sequent=new_seq)
                children.append(child)

            node.children = children
            return True

    
    return False

def print_premises(premises: list[Sequent]):
    i = 1
    for seq in premises:
        print(f"premise {i}: {seq}")
        i += 1

    
