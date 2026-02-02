from dataclasses import dataclass
from typing import FrozenSet


class Formula:
    pass


@dataclass(frozen=True)
class Prop(Formula):
    p: str

    def __str__(self):
        return self.p


@dataclass(frozen=True)
class Bot(Formula):
    def __str__(self):
        return "bot"


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"({self.left} and {self.right})"


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"({self.left} or {self.right})"


@dataclass(frozen=True)
class Imp(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"({self.left} -> {self.right})"


@dataclass(frozen=True)
class Box(Formula):
    inner: Formula

    def __str__(self):
        return f"(Box({self.inner}))"


@dataclass(frozen=True)
class Diamond(Formula):
    inner: Formula

    def __str__(self):
        return f"(Diamond({self.inner}))"


@dataclass(frozen=True)
class Label:
    name: str

    def __str__(self):
        return f"{self.name}"


class Polarity:
    IN = "in"
    OUT = "out"


@dataclass(frozen=True)
class LFormula:
    label: Label
    formula: Formula
    polarity: Polarity

    def __str__(self):
        return f"{self.label} : {self.formula} {self.polarity}"


@dataclass(frozen=True)
class Preorder:
    left: Label
    right: Label

    def __str__(self):
        return f"{self.left} <= {self.right}"

    def __repr__(self):
        return f"{self.left} <= {self.right}"


@dataclass(frozen=True)
class Relation:
    left: Label
    right: Label

    def __str__(self):
        return f"{self.left} R {self.right}"

    def __repr__(self):
        return f"{self.left} R {self.right}"


@dataclass(frozen=True)
class Sequent:
    relations: FrozenSet[Preorder]
    modal_relations: FrozenSet[Relation]
    formulas: FrozenSet[LFormula]

    def to_string(self):
        parts = []

        if self.relations:
            parts.extend(str(r) for r in self.relations)

        if self.modal_relations:
            parts.extend(str(r) for r in self.modal_relations)

        if self.formulas:
            parts.extend(str(f) for f in self.formulas)

        return "\n"+"[" + ", ".join(parts) + "]"+"\n"

    def __str__(self):
        return self.to_string()

    def __repr__(self):
        return self.to_string()

    def copy(self):
        return Sequent(
            self.relations.copy(),
            self.formulas.copy(),
            self.modal_relations.copy()
        )
    

# Compute all labels from G
def all_labels(G: Sequent) -> list[Label]:
    labels = set()  # using set for efficiency and avoiding redundancy

    for relation in G.relations:
        labels.add(relation.left)
        labels.add(relation.right)

    for formula in G.formulas:
        labels.add(formula.label)

    for r in G.modal_relations:
        labels.add(r.left)
        labels.add(r.right)

    return list(labels)


# Generate one new label at a time
def new_label(G: Sequent) -> Label:
    lst = all_labels(G)

    i = 0
    while True:
        name = f"x{i}"
        lab = Label(name)
        if lab not in lst:
            return lab
        i += 1


# Generate n new labels at a time
def fresh_labels(G: Sequent, n: int) -> list[Label]:
    used = set(all_labels(G))
    result = []
    i = 0
    while len(result) < n:
        lab = Label(f"x{i}")
        if lab not in used:
            result.append(lab)
            used.add(lab)
        i += 1
    return result


# Generate a new label from a list. NOT confused with new_label().
def new_label_list(lst: list) -> Label:
    i = 0
    while True:
        name = f"x{i}"
        lab = Label(name)
        if lab not in lst:
            return lab
        i += 1


def print_step(G: Sequent, rule_name: str, premises: list[Sequent]):
    print("Goal:")
    print(" ", G)
    print("Rule:", rule_name)
    print("Result:")

    if not premises:
        print("  []")
    else:
        for p in premises:
            print(" ", p)

    print("-" * 30)
