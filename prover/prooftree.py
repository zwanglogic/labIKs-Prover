from syntax import *
from dataclasses import dataclass, field
from typing import List, Optional
from countermodel import *

@dataclass
class ProofNode:
    sequent: Sequent
    rule: Optional[str] = None
    children: List["ProofNode"] = field(default_factory=list)

    def is_leaf(self) -> bool:
        return len(self.children) == 0


@dataclass
class ShrinkSaturationResult:
    saturation_tree: ProofNode
    shrinking_trees: list[ProofNode]
    shrunk_sequents: list[Sequent]


def print_proof_tree(node: ProofNode, prefix: str = "", is_last: bool = True, is_root: bool = True):
    # Root node: print sequent alone (no branch chars)
    if is_root:
        print(node.sequent)
        print()
        if node.rule is None:
            print("(leaf)")
            return
        print(f"  rule: {node.rule}")
        print()
    else:
        branch = "└─ " if is_last else "├─ "
        line = prefix + branch + str(node.sequent)
        if node.rule is None and not node.children:
            line += "   (leaf)"
        print(line)

        # if leaf, stop
        if node.rule is None or not node.children:
            return

        # blank line + rule
        print(prefix + ("   " if is_last else "│  "))
        print(prefix + ("   " if is_last else "│  ") + f"  rule: {node.rule}")
        print(prefix + ("   " if is_last else "│  "))

    # Prepare prefix for children
    new_prefix = prefix + ("   " if is_last else "│  ")

    # Print children recursively
    for i, child in enumerate(node.children):
        child_is_last = (i == len(node.children) - 1)
        print_proof_tree(child, prefix=new_prefix, is_last=child_is_last, is_root=False)
        if i != len(node.children) - 1:
            print()


# Export to LaTeX
def formula_to_latex(F) -> str:
    match F:
        case Prop(name):
            return name
        case Bot():
            return r"\bot"
        case And(A, B):
            return rf"({formula_to_latex(A)} \land {formula_to_latex(B)})"
        case Or(A, B):
            return rf"({formula_to_latex(A)} \lor {formula_to_latex(B)})"
        case Imp(A, B):
            return rf"({formula_to_latex(A)} \to {formula_to_latex(B)})"
        case Box(A):
            return rf"\Box {formula_to_latex(A)}"
        case Diamond(A):
            return rf"\Diamond {formula_to_latex(A)}"
        case _:
            raise NotImplementedError(f"Unknown formula: {F}")


def lformula_to_latex(f: LFormula) -> str:
    core = formula_to_latex(f.formula)
    if f.polarity == Polarity.IN:
        return rf"{f.label}:{core}^\bullet"
    else:
        return rf"{f.label}:{core}^\circ"


def preorder_to_latex(r: Preorder) -> str:
    return rf"{r.left} \le {r.right}"


def modal_relation_to_latex(r: Relation) -> str:
    return rf"{r.left} R {r.right}"


def sequent_to_latex(G: Sequent) -> str:
    parts = []

    for r in G.relations:
        parts.append(preorder_to_latex(r))

    for r in G.modal_relations:
        parts.append(modal_relation_to_latex(r))

    for f in G.formulas:
        parts.append(lformula_to_latex(f))

    return r"\; , \; ".join(parts)


RULE_LATEX = {
    "rule_id":        r"\mathsf{id}",
    "rule_bot_in":    r"\bot^\bullet",
    "rule_and_in":    r"\land^\bullet",
    "rule_and_out":   r"\land^\circ",
    "rule_or_in":     r"\lor^\bullet",
    "rule_or_out":    r"\lor^\circ",
    "rule_imp_in":    r"\to^\bullet",
    "rule_imp_out":   r"\to^\circ",
    "rule_box_in":      r"\Box^\bullet",
    "rule_box_out":     r"\Box^\circ",
    "rule_diamond_in":  r"\Diamond^\bullet",
    "rule_diamond_out": r"\Diamond^\circ",
    "rule_shrk": r"\mathsf{shrk}"
}


def rule_to_latex(rule: str) -> str:
    return RULE_LATEX.get(rule, r"\mathsf{" + rule.replace("_", r"\_") + "}")


def proofnode_to_buss(node) -> str:
    # leaf
    if node.rule is None or len(node.children) == 0:
        return rf"\AxiomC{{$ {sequent_to_latex(node.sequent)} $}}"

    parts = [proofnode_to_buss(ch) for ch in node.children]

    parts.append(
    rf"\RightLabel{{$ {rule_to_latex(node.rule)} $}}"
    )

    n = len(node.children)
    if n == 1:
        inf = rf"\UnaryInfC{{$ {sequent_to_latex(node.sequent)} $}}"
    elif n == 2:
        inf = rf"\BinaryInfC{{$ {sequent_to_latex(node.sequent)} $}}"
    elif n == 3:
        inf = rf"\TrinaryInfC{{$ {sequent_to_latex(node.sequent)} $}}"
    else:
        raise ValueError(f"Too many premises: {n}")

    parts.append(inf)
    return "\n".join(parts)


def export_proof_to_latex_document(root) -> str:
    body = proofnode_to_buss(root)
    return r"""\documentclass{article}
\usepackage{bussproofs}
\usepackage{amsmath}
\usepackage{amssymb}

\usepackage[paperwidth=65cm, paperheight=10cm, margin=2cm]{geometry} 

\begin{document}

\def\ScoreOverhang{1pt}
\def\LabelSpacing{3pt}

\pagestyle{empty}

\centering 
\vspace*{\fill} 

\begin{prooftree}
""" + body + r"""
\end{prooftree}

\vspace*{\fill} 

\end{document}
"""

def lab(x: Label) -> str:
        return str(x)


def prop(p: Prop) -> str:
        return str(p)


def model_to_latex(M: BirelationalModel) -> str:
    
    worlds = ", ".join(sorted([lab(w) for w in M.worlds]))
    le = ",\\; ".join(sorted([rf"{lab(r.left)} \le {lab(r.right)}" for r in M.preorders]))
    rrel = ",\\; ".join(sorted([rf"{lab(r.left)} R {lab(r.right)}" for r in M.modal_relations]))

    val_lines = []
    for w in sorted(M.worlds, key=lambda z: z.name):
        ps = sorted(M.valuation.get(w, set()), key=lambda p: p.p)
        inside = ", ".join([prop(p) for p in ps])
        val_lines.append(rf"V({lab(w)}) = \{{{inside}\}}")

    val = r"\\ ".join(val_lines) if val_lines else r"\text{(empty)}"

    return rf"""
\[
\mathcal{{M}} = \langle W,\le,R,V\rangle
\]
\[
W = \{{{worlds}\}}
\]
\[
\le \;=\; \{{ {le} }}
\]
\[
R \;=\; \{{ {rrel} }}
\]
\[
{val}
\]
""".strip()


def export_model_to_latex_document(M: BirelationalModel, title: str = "Countermodel") -> str:
    body = model_to_latex(M)
    return rf"""\documentclass{{article}}
\usepackage{{amsmath}}
\usepackage{{amssymb}}
\usepackage[margin=2cm]{{geometry}}
\pagestyle{{empty}}
\begin{{document}}

\section*{{{title}}}

{body}

\end{{document}}
"""