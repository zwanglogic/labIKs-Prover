from lift import *
from prooftree import *


def compute_largest_simulation(G: Sequent) -> set[tuple[Label, Label]]:
    """
    Definition 5.10 (simulation)

    Compute the largest simulation. Implemented by using the Greatest Fixed Point Algorithm.
    """
    change = True
    S = set()

    for x in all_labels(G):
        for y in all_labels(G):
            if are_equivalent_labels(G, x, y):
                S.add((x, y))

    while change == True:
        change = False

        for x, y in list(S):
            for y_hat in all_labels(G):
                found = False
                if Relation(y, y_hat) not in G.modal_relations:
                    continue
                for x_hat in all_labels(G):
                    if (Relation(x, x_hat) in G.modal_relations) and ((x_hat, y_hat) in S):
                        found = True
                        break
                if not found:
                    S.remove((x, y))
                    change = True
                    break

    return S


def uniform_substitution(G: Sequent, old: Label, new: Label) -> Sequent:
    """
    Uniformly substituting an old label for a new label in G.
    """
    new_relations = set()
    for r in G.relations:
        left = new if r.left == old else r.left
        right = new if r.right == old else r.right
        new_relations.add(Preorder(left, right))

    new_modal_relations = set()
    for r in G.modal_relations:
        left = new if r.left == old else r.left
        right = new if r.right == old else r.right
        new_modal_relations.add(Relation(left, right))

    new_formulas = set()
    for f in G.formulas:
        label = new if f.label == old else f.label
        new_formulas.add(LFormula(label, f.formula, f.polarity))

    return Sequent(
        frozenset(new_relations),
        frozenset(new_modal_relations),
        frozenset(new_formulas)
    )


def are_siblings(G: Sequent, x: Label, y: Label) -> bool:
    """
    Definition 5.11

    x|y iff there is a label z s.t. z R x and z R y.
    """
    for z in all_labels(G):
        if Relation(z, x) in G.modal_relations and Relation(z, y) in G.modal_relations:
            return True

    return False


def is_redundant(G: Sequent, y: Label, S: set[tuple[Label, Label]]) -> bool:
    """
    Definition 5.11

    Here we can simply use the largest simulation.
    """
    for x in all_labels(G):
        if x == y:
            continue

        if are_siblings(G, x, y) and (x, y) in S:
            return True

    return False


def is_shrunk(G: Sequent, S: set[tuple[Label, Label]]) -> bool:
    """
    Definition 5.11

    Here we can simply use the largest simulation.
    """
    for x in all_labels(G):
        if is_redundant(G, x, S):
            return False
    return True


def rule_shrk(G: Sequent, S: set[tuple[Label, Label]]) -> Sequent | None:
    """
    Apply one shrinking step to G if possible.
    """
    for y in all_labels(G):
        for x in all_labels(G):
            if x == y:
                continue
            if are_siblings(G, x, y) and (x, y) in S:
                return uniform_substitution(G, old=y, new=x)

    return None


def shrinking(G: Sequent) -> Sequent:
    """
    Apply rule shrk multiple times until the leaf is shrunk.

    Remark: G is shrunk <=> we cannot apply shrk on G.

    So there is a cleaner way to implement this notion. But now, I choose to follow the definition strictly.
    """
    seq = G
    S = compute_largest_simulation(seq)

    while True:
        if is_shrunk(seq, S):
            return seq

        S = compute_largest_simulation(seq)
        nxt = rule_shrk(seq, S)

        if nxt is None:
            # In principal this is not possible.
            raise RuntimeError(
                "Sequent is not shrunk, but no applicable shrinking step exists."
            )

        seq = nxt


def collect_leaves(node: ProofNode) -> list[Sequent]:
    """
    Colloct all leaves in the prood tree.
    """
    if not node.children:
        return [node.sequent]

    leaves = []
    for child in node.children:
        leaves.extend(collect_leaves(child))
    return leaves


def shrink_saturation(G: Sequent) -> list[Sequent]:
    """
    Compute the saturation of G, then shrink every leaf sequent.
    """
    sat_tree = saturation_with_tree(G)
    leaves = collect_leaves(sat_tree)

    result = []
    for H in leaves:
        shrunk = shrinking(H)
        result.append(shrunk)

    return result


def shrinking_with_tree(G: Sequent) -> ProofNode:
    """
    Build a unary proof tree for repeated applications of rule_shrk,
    until no more shrinking step is possible.
    """
    cur = closure(G)
    root = ProofNode(sequent=cur)
    node = root

    while True:
        S = compute_largest_simulation(cur)
        nxt = rule_shrk(cur, S)

        if nxt is None:
            return root

        nxt = closure(nxt)

        child = ProofNode(sequent=nxt)
        node.rule = "rule_shrk"
        node.children = [child]

        node = child
        cur = nxt


def shrink_saturation_with_trees(G: Sequent):
    """
    Run saturation once, export its proof tree,
    then for each leaf, run shrinking and export the shrinking tree.
    """
    sat_tree = saturation_with_tree(G)
    latex = export_proof_to_latex_document(sat_tree)
    with open("saturation.tex", "w") as f:
        f.write(latex)
    leaves = collect_leaves(sat_tree)

    for i, leaf in enumerate(leaves):
        shr_tree = shrinking_with_tree(leaf)
        latex = export_proof_to_latex_document(shr_tree)
        with open(f"shrinking_leaf_{i}.tex", "w") as f:
            f.write(latex)
