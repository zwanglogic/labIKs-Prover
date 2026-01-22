from syntax import *
from happy import *
from rules import *
from closure import *
from saturation import *
from layer import *

# Generate a fresh label given a set of labels
def fresh_label_from_used(used: set[Label]) -> Label:
    i = 0
    while True:
        lab = Label(f"x{i}")
        if lab not in used:
            
            return lab
        i += 1

# Map a set of labels to a entirely new set of labels
def layer_mapping(G : Sequent, layer : set[Label]) -> dict[Label, Label]:
    used = {lab for lab in all_labels(G)}
    mapping = {}

    # The layer is a set, so we sort it for convenience
    ordered_layer = sorted(layer, key=lambda l: l.name)

    for old in ordered_layer:
        new = fresh_label_from_used(used)
        mapping[old] = new
        used.add(new)
    return mapping


def lift_base(G : Sequent, x : Label, layer: set[Label], mapping: dict[Label, Label]) -> Sequent:
    assert is_almost_happy_sequent(G), f"The input sequent {G} is not almost happy"
    assert x in layer, f"the label {x} is not in the layer {layer}"
    
    labels = all_labels(G)

    new_relations = []
    new_formulas = []
    
    # Condition 1
    for l in mapping.values():
       new_relations.append(Preorder(l,l))

    # Condition 2
    for w in labels:
        for old_y, new_y in mapping.items():
            if Preorder(w,old_y) in G.relations:
                new_relations.append(Preorder(w, new_y))
    
    # Condition 3: TBC
    
    # Condition 4
    for f in G.formulas:
        if f.label in mapping and f.polarity == Polarity.IN:
            new_y = mapping[f.label]
            content = f.formula
            new_formulas.append(LFormula(new_y, content, Polarity.IN))

    return Sequent(
        G.relations.copy() + new_relations,
        G.formulas.copy() + new_formulas
    )

def unique_extend(x : list, y : list):
    for i in y:
        if i not in x:
            x.append(i)


def lifting(G: Sequent, f: LFormula, layer: set[Label]) -> Sequent:
    assert not is_happy_formula(G, f), f"{f} is not an unhappy formula"

    match f:
        case LFormula(x, Imp(A, B), Polarity.OUT):

            mapping = layer_mapping(G, layer)
            x_hat = mapping[x]

            seq = lift_base(G, x, layer, mapping)

            unique_extend(
                seq.formulas,
                [
                    LFormula(x_hat, A, Polarity.IN),
                    LFormula(x_hat, B, Polarity.OUT)
                ]
            )

            return seq

    raise NotImplementedError("lifting only implemented for Imp_out")