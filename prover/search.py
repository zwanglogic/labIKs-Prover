from rules import *
from closure import *
from syntax import *
from layer import *
from lift import *
from saturation import *


# If the sequent is initial
def is_axiomatic(G : Sequent) -> bool:
    # bot rule
    for f in G.formulas:
        match f:
            case LFormula(label = l, formula = Bot(), polarity = Polarity.IN):
                return True
            
    # id rule
    for f1 in G.formulas:
        match f1:
            case LFormula(label = l1, formula = Prop(p1), polarity = Polarity.IN):
                for f2 in G.formulas:
                    match f2:
                        case LFormula(label = l2, formula = Prop(p2), polarity = Polarity.OUT) if l1 == l2 and p1 == p2:
                            return True

    return False

def proof_search(F : Formula) -> bool:

    # Step 0
    r = Label("r")
    initial_form = LFormula(r, F, Polarity.OUT)
    initial_rel = Preorder(r,r)
    G0 = Sequent([initial_rel], [initial_form])

    S = saturate(G0)

    while True:
        # Step 1: If all sequents in S are axiomatic, then terminate.
        if all(is_axiomatic(G) for G in S):
            return True   # provable
        # Step 2: Otherwise, pick a non-axiomatic sequent Gi from S
        Gi = next(G for G in S if not is_axiomatic(G))

        allowed = [
            f for f in Gi.formulas
            if is_allowed_formula(Gi, f)
        ]
        if allowed:
            target_f = allowed[0]
            
            current_layer = {target_f.label}
            
            G_lifted = lifting(Gi, target_f, current_layer)

            S.remove(Gi) 
            
            new_leaves = saturate(G_lifted)
            
            for leaf in new_leaves:
                if leaf not in S:
                    S.append(leaf)
                    
        else:
            return False  # not provable 


# Collect all leaf nodes from a proof tree
def collect_leaves(root: ProofNode) -> list[ProofNode]:

    leaves = []
    stack = [root]

    while stack:
        node = stack.pop()
        if not node.children:   
            leaves.append(node)
        else:
            stack.extend(node.children)

    return leaves


def proof_search_visual(F: Formula) -> bool: 
    r = Label("r")
    G0 = Sequent(
        [Preorder(r, r)],
        [LFormula(r, F, Polarity.OUT)]
    )

    step = 0 

    print(f"--- Step {step}: Initial Saturation ---")
    tree = saturation_with_tree(G0)
    
    with open(f"proof_step_{step}.tex", "w") as f:
        f.write(export_proof_to_latex_document(tree))
    
    leaves = collect_leaves(tree)
    S = [leaf.sequent for leaf in leaves]

    while True:
        if all(is_axiomatic(G) for G in S):
            print("Provable.")
            return True

        Gi = next(G for G in S if not is_axiomatic(G))

        allowed = [
            f for f in Gi.formulas
            if is_allowed_formula(Gi, f)
        ]

        if not allowed:
            print("Not provable.")
            return False

        # Lifting
        step += 1 
        target_f = allowed[0]
        current_layer = {target_f.label}

        print(f"\n--- Step {step}: Lifting ---")
        G_lifted = lifting(Gi, target_f, current_layer)

        print("--- Saturation After Lifting ---")
        tree = saturation_with_tree(G_lifted)

        with open(f"proof_step_{step}.tex", "w") as f:
            f.write(export_proof_to_latex_document(tree))
        
        print(f"LaTeX written to proof_step_{step}.tex")

        new_leaves = collect_leaves(tree)

        S.remove(Gi)
        for leaf in new_leaves:
            if leaf.sequent not in S:
                S.append(leaf.sequent)
        
