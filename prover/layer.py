from syntax import *

# without modality, all_layers(G) = [{x} | x is label appearing in G}]
def all_layers(G : Sequent):
    return [{x} for x in all_labels(G)]