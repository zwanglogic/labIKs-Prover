from syntax import *


@dataclass
class BirelationalModel:
    worlds: set[Label]
    preorders: set[Preorder]
    modal_relations: set[Relation]
    valuation: dict[Label, set[Prop]]


def sequent_to_model(G: Sequent) -> BirelationalModel:
    worlds = set(all_labels(G))
    preorders = G.relations
    modal_relations = G.modal_relations

    valuation = {}
    for w in worlds:
        valuation[w] = {
            f.formula
            for f in G.formulas
            if f.label == w and f.polarity == Polarity.IN and isinstance(f.formula, Prop)
        }

    return BirelationalModel(worlds, preorders, modal_relations, valuation)