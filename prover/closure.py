from syntax import *

# Given a sequent, for each label appears in it, adding reflexivity relation
def reflexivity(G : Sequent):
    lst = all_labels(G)

    for x in lst:
        rel = Preorder(x,x)
        if rel not in G.relations:
            G.relations.append(rel)
            flag = True
    
    

    