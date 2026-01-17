from syntax import *
from happy import *
from rules import *
from closure import *
from saturation import *
from layer import *

# generate a fresh label given a set of labels
def fresh_label_from_used(used: set[Label]) -> Label:
    i = 0
    while True:
        lab = Label(f"x{i}")
        if lab not in used:
            
            return lab
        i += 1

# map a set of labels to a entirely new set of labels
def layer_mapping(G : Sequent, layer : set[Label]) -> dict[Label, Label]:
    used = {lab for lab in all_labels(G)}
    mapping = {}

    # the layer is a set, so we sort it for convenience
    ordered_layer = sorted(layer, key=lambda l: l.name)

    for old in ordered_layer:
        new = fresh_label_from_used(used)
        mapping[old] = new
        used.add(new)
    return mapping



def lift_base(G : Sequent, x : Label, layer: set[Label]) -> Sequent:
    assert is_almost_happy_sequent(G), f"The input sequent {G} is not almost happy"
    assert x in layer, f"the label {x} is not in the layer {layer}"
    
    pass
    
    