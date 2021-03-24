from z3 import ForAll, Implies, Int, IntSort
from my_solver import MySolver

if __name__ == "__main__":
    C = 1
    D = 2

    s = MySolver()

    A = s.Function("A", IntSort(), IntSort())
    S = s.Function("S", IntSort(), IntSort())
    W = s.Function("W", IntSort(), IntSort())

    x, y = Int("x"), Int("y")

    s.add(ForAll([x, y], Implies(x <= y, A(x) <= A(y))))
    s.add(ForAll([x, y], Implies(x <= y, S(x) <= S(y))))
    s.add(ForAll([x, y], Implies(x <= y, W(x) <= W(y))))

    s.add(ForAll([x], S(x) <= A(x)))
    s.add(ForAll([x], S(x) <= C * x - W(x)))
    s.add(ForAll([x], S(x + D) >= C * x - W(x)))
    # s.add(ForAll([x], Implies(W(x) > W(x-1), A(x) <= C * x - W(x))))

    print(s.to_smt2())
    sat = s.check()
    print(sat)
    if sat == "sat":
        print(s.model())
