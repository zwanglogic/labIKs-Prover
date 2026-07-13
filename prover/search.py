from rules import *
from closure import *
from syntax import *
from layer import *
from lift import *
from saturation import *
from shrinking import *
from countermodel import *


def find_layer_bijection(G: Sequent, L1: set[Label], L2: set[Label]) -> dict[Label, Label] | None:
    for f in all_bijections(L1, L2):
        if all(are_equivalent_labels(G, x, f[x]) for x in L1) and \
           all((Relation(x, y) in G.modal_relations) ==
               (Relation(f[x], f[y]) in G.modal_relations)
               for x in L1 for y in L1):
            return f
    return None


def layer_formulas(G: Sequent, L: set[Label]) -> list[LFormula]:
    return [formula for formula in G.formulas if formula.label in L]


def repair_for_countermodel(G: Sequent) -> Sequent:
    seq = closure(G)

    while not is_happy_sequent(seq):
        E = compute_equiv_relation(seq)
        layers = list(all_layers(seq, E))

        unhappy_layers = [
            L for L in layers
            if any(
                f.label in L and not is_happy_formula(seq, f)
                for f in seq.formulas
            )
        ]

        L = next(
            (
                L for L in unhappy_layers
                if not any(
                    Lp != L and order_layer(seq, Lp, L)
                    for Lp in unhappy_layers
                )
            ),
            None,
        )

        if L is None:
            raise RuntimeError("No minimal unhappy layer found")

        bijection = next(
            (
                f
                for lower in layers
                if lower != L and order_layer(seq, lower, L)
                for f in [find_layer_bijection(seq, L, lower)]
                if f is not None
            ),
            None,
        )

        if bijection is None:
            raise RuntimeError("No equivalent lower layer found")

        seq = closure(
            Sequent(
                frozenset(
                    set(seq.relations)
                    | {Preorder(v, bijection[v]) for v in L}
                ),
                seq.modal_relations,
                seq.formulas,
            )
        )

    return seq

# If the sequent is initial
def is_axiomatic(G: Sequent) -> bool:
    # bot rule
    for f in G.formulas:
        match f:
            case LFormula(label=l, formula=Bot(), polarity=Polarity.IN):
                return True

    # id rule
    for f1 in G.formulas:
        match f1:
            case LFormula(label=l1, formula=Prop(p1), polarity=Polarity.IN):
                for f2 in G.formulas:
                    match f2:
                        case LFormula(label=l2, formula=Prop(p2), polarity=Polarity.OUT) if l1 == l2 and p1 == p2:
                            return True

    return False


def proof_search_visual(F: Formula) -> bool:
    """
    Visual proof search with shrink-saturation and lifting.
    Generates LaTeX proof trees for every saturation and shrinking step.
    """
    r = Label("r")

    G0 = Sequent(
        frozenset({Preorder(r, r)}),
        frozenset(),
        frozenset({LFormula(r, F, Polarity.OUT)})
    )

    step = 0

    # Initial shrink-saturation
    result = shrink_saturation_with_trees(G0)
    print(f"---------------- Step {step}: Initial shrink-saturation ----------------\n")

    # Export initial saturation tree
    with open(f"step_{step}_saturation.tex", "w") as f:
        f.write(export_proof_to_latex_document(result.saturation_tree))

    # Export initial shrinking trees
    for i, shr_tree in enumerate(result.shrinking_trees):
        with open(f"step_{step}_shrinking_leaf_{i}.tex", "w") as f:
            f.write(export_proof_to_latex_document(shr_tree))

    S = result.shrunk_sequents

    while True:
        if all(is_axiomatic(G) for G in S):
            print("Provable :D")
            return True

        # Pick a non-axiomatic leaf
        Gi = next(G for G in S if not is_axiomatic(G))
        print(f"Current sequent is \n{Gi}\n")

        E = compute_equiv_relation(Gi)

        allowed = [
            f for f in Gi.formulas
            if is_allowed_formula(Gi, f, E)
        ]

        if not allowed:

            Gi_repaired = repair_for_countermodel(Gi)

            # Export the countermodel
            model = sequent_to_model(Gi_repaired)
            tex = export_model_to_latex_document(model, title=f"Countermodel at step {step}")
            with open(f"countermodel.tex", "w") as f:
                f.write(tex)

            print("Not provable.\nA countermodel has been generated.")
            return False

        # Lifting
        step += 1
        target_f = allowed[0]
        current_layer = layer(Gi, E, target_f.label)

        G_lifted = lifting(Gi, target_f, current_layer)

        lift_tree = lifting_with_tree(Gi, target_f, current_layer)
        with open(f"step_{step}_lift.tex", "w") as f:
            f.write(export_proof_to_latex_document(lift_tree))
        print(f"------------------------ Step {step}: Lifting ------------------------\n")

        # Shrink-saturation
        lift_result = shrink_saturation_with_trees(G_lifted)
        print("---------------- Shrink-Saturation After Lifting ----------------\n")

        # Export saturation tree
        with open(f"step_{step}_saturation.tex", "w") as f:
            f.write(export_proof_to_latex_document(
                lift_result.saturation_tree))

        # Export shrinking trees after lifting
        for i, shr_tree in enumerate(lift_result.shrinking_trees):
            with open(f"step_{step}_shrinking_leaf_{i}.tex", "w") as f:
                f.write(export_proof_to_latex_document(shr_tree))

        S.remove(Gi)
        for seq in lift_result.shrunk_sequents:
            if seq not in S:
                S.append(seq)