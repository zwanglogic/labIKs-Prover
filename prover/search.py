from rules import *
from closure import *
from syntax import *
from layer import *
from lift import *
from saturation import *
from shrinking import *
from countermodel import *


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
    print(f"--- Step {step}: Initial shrink-saturation ---")

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
            print("Provable.")
            return True

        # Pick a non-axiomatic leaf
        Gi = next(G for G in S if not is_axiomatic(G))

        E = compute_equiv_relation(Gi)

        allowed = [
            f for f in Gi.formulas
            if is_allowed_formula(Gi, f, E)
        ]

        if not allowed:

            # Export the countermodel
            model = sequent_to_model(Gi)
            tex = export_model_to_latex_document(model, title=f"Countermodel at step {step}")
            with open(f"countermodel_step_{step}.tex", "w") as f:
                f.write(tex)

            print("Not provable.")
            return False

        # Lifting
        step += 1
        target_f = allowed[0]
        current_layer = layer(Gi, E, target_f.label)

        G_lifted = lifting(Gi, target_f, current_layer)
        print(f"\n--- Step {step}: Lifting ---")

        # Shrink-saturation
        lift_result = shrink_saturation_with_trees(G_lifted)
        print("--- Shrink-Saturation After Lifting ---")

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


# Example B.2
p = Prop("p")
q = Prop("q")
F = Imp(Imp(Diamond(p), Box(q)), Box(Imp(p, q)))

a = Prop("a")
b = Prop("b")


F = Imp(Imp(Imp(a, Box(b)), Bot()), Bot())

result = proof_search_visual(F)
print(result)
