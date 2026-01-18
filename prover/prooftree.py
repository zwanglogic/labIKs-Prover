from syntax import *
from rules import *

from dataclasses import dataclass, field
from typing import List, Optional

@dataclass
class ProofNode:
    sequent: Sequent
    rule: Optional[str] = None
    children: List["ProofNode"] = field(default_factory=list)

    def is_leaf(self) -> bool:
        return len(self.children) == 0

def print_proof_tree(node: ProofNode):
    # print parent node
    print(node.sequent)
    print()

    if node.rule is None:
        print("(leaf)")
        return

    # print rule
    print(f"  rule: {node.rule}")
    print()

    # print children
    for i, child in enumerate(node.children):
        is_last = (i == len(node.children) - 1)
        branch = "└─ " if is_last else "├─ "

        line = branch + str(child.sequent)
        if child.rule is None:
            line += "   (leaf)"

        print(line)

        if not is_last:
            print()

    