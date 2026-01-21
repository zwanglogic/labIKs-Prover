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
        return f"{self.left} and {self.right}"


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"{self.left} or {self.right}"


@dataclass(frozen=True)
class Imp(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"{self.left} -> {self.right}"


@dataclass(frozen=True)
class Label:
    name : str
    
    def __str__(self):
        return f"{self.name}"


class Polarity:
    IN = "in"
    OUT = "out"


@dataclass(frozen=True)
class LFormula:
    label : Label
    formula : Formula
    polarity : Polarity

    def __str__(self):
        return f"{self.label} : {self.formula} {self.polarity}"
    

@dataclass(frozen=True)
class Preorder:
    left : Label
    right : Label

    def __str__(self):
        return f"{self.left} <= {self.right}"
    
    def __repr__(self):
        return f"{self.left} <= {self.right}"
    

@dataclass(frozen=True)
class Sequent:
    relations: FrozenSet[Preorder]
    formulas: FrozenSet[LFormula]

    def to_string(self):
        s = "["

        if len(self.relations) > 0:
            last = self.relations[-1]
            for r in self.relations:
                s += str(r)
                if r != last:
                    s += ", "

            if len(self.formulas) > 0:
                s += ", "

        if len(self.formulas) > 0:
            last = self.formulas[-1]
            for f in self.formulas:
                s += str(f)
                if f != last:
                    s += ", "

        s += "]"
        return s
    
    def __str__(self):
        return self.to_string()
    
    def __repr__(self):
        return self.to_string()
    
    def copy(self):
        return Sequent(
            self.relations.copy(),
            self.formulas.copy()
        )
    

def all_labels(G : Sequent) -> list[Label]:
    lst = []

    for relation in G.relations:
        if relation.left not in lst:
            lst.append(relation.left)
        if relation.right not in lst:
            lst.append(relation.right)
    
    for formula in G.formulas:
        if formula.label not in lst:
            lst.append(formula.label)
    
    return lst


def new_label(G : Sequent) -> Label:
    lst = all_labels(G)

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