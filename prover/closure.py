from syntax import *

# Given a sequent, for each label appears in it, adding reflexivity relation
def reflexivity(G : Sequent):
    lst = all_labels(G)

    for x in lst:
        rel = Preorder(x,x)
        if rel not in G.relations:
            G.relations.append(rel)
            flag = True
    
# transitive closure
def transitivity(G: Sequent):
    changed = False
    rel = G.relations.copy()

    for r1 in rel:
        for r2 in rel:
            if r1.right == r2.left:
                r3 = Preorder(r1.left, r2.right)
                if r3 not in G.relations:
                    G.relations.append(r3)
                    changed = True

    if changed:
        transitivity(G)

# reflexive transitive closure
def closure(G: Sequent) -> Sequent:
    newG = Sequent(G.relations.copy(), G.formulas.copy())

    old_size = -1
    while old_size != len(newG.relations):
        old_size = len(newG.relations)
        reflexivity(newG)
        transitivity(newG)

    return newG

# test
x = Label("x")
y = Label("y")

G = Sequent([], [
    LFormula(x, Prop("P"), Polarity.IN),
    LFormula(y, Prop("Q"), Polarity.OUT),
])

G = closure(G)
print(G.relations)


x = Label("x")
y = Label("y")
z = Label("z")

G = Sequent([
    Preorder(x, y),
    Preorder(y, z)
], [])

G = closure(G)

for r in G.relations:
    print(r)
    