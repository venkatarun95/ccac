from z3 import Or

from cache import run_query
from model import make_solver
from config import ModelConfig


def prove_steady_state(timeout=10):
    # This analysis is for infinite buffer size

    c = ModelConfig.default()
    c.cca = "copa"
    # We only need compose=False to prove cwnd increases/doesn't
    # fall. Otherwise, this assumption is not needed (of course, we *can* make
    # the assumption if we want)
    c.compose = True
    c.calculate_qdel = True

    # The last cwnd value that is chosen completely freely
    dur = c.R + c.D - 1

    # If cwnd > 4 BDP + alpha, cwnd wil decrease by at-least alpha
    s, v = make_solver(c)
    s.add(v.c_f[0][dur] > 4*c.C*c.R + v.alpha)
    s.add(v.c_f[0][-1] >= v.c_f[0][dur] - v.alpha)
    s.add(v.L[0] == 0)
    s.add(v.alpha < (1 / 3) * c.C * c.R)
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # If queue length is > 4 BDP + 2 alpha and cwnd < 4 BDP + alpha, queue
    # length decreases by at-least alpha
    s, v = make_solver(c)
    s.add(v.c_f[0][dur] <= 4*c.C*c.R + v.alpha)
    s.add(v.A[0] - v.S[0] > 4*c.C*c.R + 2*v.alpha)
    s.add(v.A[-1] - v.S[-1] > v.A[0] - v.S[0] - v.alpha)
    s.add(v.L[0] == 0)
    s.add(v.alpha < (1 / 5) * c.C * c.R)
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # If cwnd < BDP - alpha and queue length < 4 BDP + 2 alpha, cwnd increases
    # by at-least alpha
    c.T = 15
    c.compose = False  # we definitely need it to prove cwnd increases
    s, v = make_solver(c)
    s.add(v.c_f[0][dur] < c.C*c.R - v.alpha)
    s.add(v.A[0] - v.S[0] <= 4*c.C*c.R + 2*v.alpha)
    s.add(v.c_f[0][-1] < v.c_f[0][dur] + v.alpha)
    s.add(v.c_f[0][-1] < c.C*c.R - v.alpha)
    s.add(v.L[0] == 0)
    s.add(v.alpha < (1 / 4) * c.C * c.R)
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # If Copa has entered steady state, it does not leave it
    c.T = 10
    c.compose = False
    s, v = make_solver(c)
    ors = []
    s.add(v.c_f[0][dur] >= c.C*c.R - v.alpha)
    ors.append(v.c_f[0][-1] < c.C*c.R - v.alpha)
    s.add(v.c_f[0][dur] <= 4*c.C*c.R + 2*v.alpha)
    ors.append(v.c_f[0][-1] > 4*c.C*c.R + v.alpha)
    s.add(v.A[0] - v.S[0] <= 4*c.C*c.R + 2*v.alpha)
    ors.append(v.A[-1] - v.S[-1] > 4*c.C*c.R + 2*v.alpha)

    s.add(v.alpha < (1 / 7) * c.C * c.R)
    s.add(v.L[0] == 0)
    s.add(Or(*ors))
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")


if __name__ == "__main__":
    prove_steady_state()
