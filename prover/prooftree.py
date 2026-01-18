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

def print_proof_tree(node: ProofNode, prefix: str = "", is_last: bool = True, is_root: bool = True):
    # Root node: print sequent alone (no branch chars)
    if is_root:
        print(node.sequent)
        print()
        if node.rule is None:
            print("(leaf)")
            return
        print(f"  rule: {node.rule}")
        print()
    else:
        branch = "└─ " if is_last else "├─ "
        line = prefix + branch + str(node.sequent)
        if node.rule is None and not node.children:
            line += "   (leaf)"
        print(line)

        # if leaf, stop
        if node.rule is None or not node.children:
            return

        # blank line + rule
        print(prefix + ("   " if is_last else "│  "))
        print(prefix + ("   " if is_last else "│  ") + f"  rule: {node.rule}")
        print(prefix + ("   " if is_last else "│  "))

    # Prepare prefix for children
    new_prefix = prefix + ("   " if is_last else "│  ")

    # Print children recursively
    for i, child in enumerate(node.children):
        child_is_last = (i == len(node.children) - 1)
        print_proof_tree(child, prefix=new_prefix, is_last=child_is_last, is_root=False)
        if i != len(node.children) - 1:
            print()

    