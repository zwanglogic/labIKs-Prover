from syntax import *
from search import *

def main():
    # Example B.2
    p = Prop("p")
    q = Prop("q")
    F = Imp(Imp(Diamond(p), Box(q)), Box(Imp(p, q)))

    a = Prop("a")
    b = Prop("b")


    F = Imp(Imp(Imp(a, Box(b)), Bot()), Bot())

    result = proof_search_visual(F)
    print(result)

if __name__ == "__main__":
    main()