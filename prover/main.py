import argparse

from syntax import *
from search import proof_search_visual

def main():
    parser = argparse.ArgumentParser(
        description="LabIKs Prover"
    )

    parser.add_argument(
        "--formula",
        type=str,
        required=True,
    )

    args = parser.parse_args()

    env = {
        "Prop": Prop,
        "And": And,
        "Or": Or,
        "Imp": Imp,
        "Box": Box,
        "Diamond": Diamond,
        "Bot": Bot,
    }

    try:
        F = eval(args.formula, {}, env)
    except Exception as e:
        print("Error parsing formula.")
        print(e)
        return

    print("-------------------------- labIKs Prover --------------------------\n")
    print(f"Input formula: {F}\n")

    proof_search_visual(F)

if __name__ == "__main__":
    main()