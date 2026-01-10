from syntax import *

# list of rules in LabIKs
# each rule is a fuction of type Sequent -> list[Sequent]
RULES = [
    rule_id,
    rule_bot,
    rule_and_in,
    rule_and_out,
    rule_or_in,
    rule_or_out,
    rule_imp_in,
    rule_imp_out,
    rule_rf,
    rule_tr,
]

def apply_rules(G : Sequent) -> list[Sequent]:
    for rule in RULES:
        x = rule(G) # x is the resulf of application of the rule

        if x: 
            return x # successfully apply
        
    return [] # no rule can be applied
    
