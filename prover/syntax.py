from dataclasses import dataclass

# Formulas

class Formula:
   pass


@dataclass
class Prop(Formula):
    p: str

    def __str__(self):
        return self.p


@dataclass
class Bot(Formula):
    def __str__(self):
        return "bot"


@dataclass
class And(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"{self.left} and {self.right}"


@dataclass
class Or(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"{self.left} or {self.right}"


@dataclass
class Imp(Formula):
    left: Formula
    right: Formula

    def __str__(self):
        return f"{self.left} -> {self.right}"


#  test   
A = Prop("A")
B = Prop("B")

f = Imp(A, Or(Bot(), And(A, B)))

print(f)       


# Labels


@dataclass
class Label:
    name : str
    
    def __str__(self):
        return f"{self.name}"

# Polarity          


class Polarity:
    IN = "in"
    OUT = "out"


# Labelled formulas


@dataclass
class LFormula:
    label : Label
    formula : Formula
    polarity : Polarity

    def __str__(self):
        return f"{self.label} : {self.formula} {self.polarity}"
    

    
#test 

x = Label("x")
p = Prop("P")

f2 = LFormula(x, p, Polarity.IN)
print(f2)


# Preorder relation

@dataclass
class Preorder:
    left : Label
    right : Label

    def __str__(self):
        return f"{self.left} <= {self.right}"
    
    def __repr__(self):
        return f"{self.left} <= {self.right}"
    

# test
x = Label("x")
y = Label("y")

f = Preorder(x,y)
print(f)


# Sequent


@dataclass
class Sequent:
    relations : list[Preorder]
    formulas : list[LFormula]

    def to_string(self):
        s = "["

        if len(self.relations) > 0:
            last = self.relations[-1]
            for r in self.relations:
                s += r.__str__()
                s += ", "

        if len(self.formulas) > 0:
            last = self.formulas[-1]
            for f in self.formulas:
                s += f.__str__()
                if f != last:
                    s += ", "
        s = s + "]"
        return s
    
    def __str__(self):
        return self.to_string()
    
    def __repr__(self):
        return self.to_string()
    
# test
s = Sequent([Preorder(x,y)],[A,f])
print(s)

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
