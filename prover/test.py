from syntax import *
from rules import *
from search import *


x = Label("x")
p = Prop("p")
q = Prop("q")


phi = Or(p, q)


G = Sequent([], [
    LFormula(x, phi, Polarity.IN),
    LFormula(x, p, Polarity.OUT),
])

print("Initial goal:")
print(G)
print()


result = dfs_search(G)

print("Proved?" , result)