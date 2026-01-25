from syntax import *
from happy import *
from rules import *
from closure import *
from saturation import *
from layer import *


def layer_mapping(G: Sequent, layer: set[Label]) -> dict[Label, Label]:
    """
    Construction 5.8 (Lifting)

    Generate a set of fresh labels from a given set of labels. In our content:

    Mapping L = {y_1,...,y_l} to L' = {y_1',...,y_l'}.
    """

    # The layer is a set, so we sort it for convenience
    ordered_layer = sorted(layer, key=lambda l: l.name)

    num = len(ordered_layer)

    new_layer = fresh_labels(G, num)

    return dict(zip(ordered_layer, new_layer))


def lift_base(G: Sequent, x: Label, layer: set[Label], mapping: dict[Label, Label]) -> Sequent:
    """
    Construction 5.8 (Lifting)

    Construct G↑x according to 5.8.

    Reminder: always do closure() after call this function.
    """
    assert is_almost_happy_sequent(
        G), f"The input sequent {G} is not almost happy"
    assert x in layer, f"the label {x} is not in the layer {layer}"

    labels = all_labels(G)

    new_relations = set()
    new_formulas = set()
    new_modal_relation = set()

    # Condition 1
    for l in mapping.values():
        new_relations.add(Preorder(l, l))

    # Condition 2
    for w in labels:
        for old_y, new_y in mapping.items():
            if Preorder(w, old_y) in G.relations:
                new_relations.add(Preorder(w, new_y))

    # Condition 3
    for y in mapping:
        for z in mapping:
            if Relation(y, z) in G.modal_relations:
                new_modal_relation.add(Relation(mapping[y], mapping[z]))

    # Condition 4
    for f in G.formulas:
        if f.label in mapping and f.polarity == Polarity.IN:
            new_y = mapping[f.label]
            content = f.formula
            new_formulas.add(LFormula(new_y, content, Polarity.IN))

    return Sequent(
        frozenset(G.relations | new_relations),
        frozenset(G.modal_relations | new_modal_relation),
        frozenset(G.formulas | new_formulas)
    )


def lifting(G: Sequent, f: LFormula, layer: set[Label]) -> Sequent:
    """
    Compute the lifting of G↑ x:F ◦, where x:F ◦ in is an unhappy formula of form 

    F = Imp(A, B) or F = Box(B)
    """
    assert not is_happy_formula(G, f), f"{f} is not an unhappy formula"

    match f:
        case LFormula(x, Imp(A, B), Polarity.OUT):

            mapping = layer_mapping(G, layer)
            x_hat = mapping[x]

            seq = lift_base(G, x, layer, mapping)

            formulas = set(seq.formulas)

            formulas.add(LFormula(x_hat, A, Polarity.IN))
            formulas.add(LFormula(x_hat, B, Polarity.OUT))

            return Sequent(seq.relations, seq.modal_relations, frozenset(formulas))

        case LFormula(x, Box(B), Polarity.OUT):

            mapping = layer_mapping(G, layer)
            x_hat = mapping[x]

            seq = lift_base(G, x, layer, mapping)

            formulas = set(seq.formulas)
            relations = set(seq.relations)
            modal_relations = set(seq.modal_relations)

            z = new_label(seq)

            formulas.add(LFormula(z, B, Polarity.OUT))
            relations.add(Preorder(z, z))
            modal_relations.add(Relation(x_hat, z))

            return Sequent(frozenset(relations), frozenset(modal_relations), frozenset(formulas))

    raise NotImplementedError(
        "lifting only implemented for Imp_out and Box_out")
