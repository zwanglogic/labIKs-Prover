from syntax import *

# without modality, layer(G) = [{x} | x is label appearing in G}]
def layer(G : Sequent):
    return [{x} for x in all_labels(G)]