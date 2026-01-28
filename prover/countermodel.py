from syntax import *


@dataclass
class BirelationalModel:
    worlds: set[Label]
    preorders: set[Preorder]
    modal_relations: set[Relation]
    valuation: dict[Label, set[Prop]]


def sequent_to_model(G: Sequent) -> BirelationalModel:
    """
    Extract a birelational countermodel from a sequent.

    Definition 2.2. (W, <=, R, V)

    - W consists of all labels occurring in G.
    - <= is given directly by the preorder relations in G.
    - R is given directly by the modal relations in G.
    - V(x) = { p | x : p is marked with polarity IN in G }.
    """
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