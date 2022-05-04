from z3 import And, Or

from config import ModelConfig
from model import make_solver
from pyz3_utils import run_query


def prove_steady_state(timeout=10):
    # This analysis is for infinite buffer size

    c = ModelConfig.default()
    c.cca = "copa"
    # We only need compose=False to prove cwnd increases/doesn't
    # fall. Otherwise, this assumption is not needed (of course, we *can* make
    # the assumption if we want)
    c.compose = True
    c.calculate_qdel = True

    # The last cwnd value that is chosen completely freely. We'll treat this as
    # the initial cwnd
    dur = c.R + c.D - 1

    # If cwnd > 4 BDP + alpha, cwnd wil decrease by at-least alpha
    s, v = make_solver(c)
    # Lemma's assumption
    # We are looking at infinite buffer, no loss case here and in the paper
    s.add(And(v.L[0] == 0, v.L[-1] == 0))
    s.add(v.alpha < (1 / 3) * c.C * c.R)
    s.add(v.c_f[0][dur] > 4*c.C*c.R + v.alpha)
    # Lemma's statement's converse
    s.add(v.c_f[0][-1] >= v.c_f[0][dur] - v.alpha)
    print("Proving that cwnd will decrease when it is too big")
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # If queue length is > 4 BDP + 2 alpha and cwnd < 4 BDP + alpha, queue
    # length decreases by at-least alpha and cwnd will not increase its bound
    s, v = make_solver(c)
    # Lemma's assumption
    s.add(And(v.L[0] == 0, v.L[-1] == 0))
    s.add(v.alpha < (1 / 5) * c.C * c.R)
    s.add(v.c_f[0][dur] <= 4*c.C*c.R + v.alpha)
    s.add(v.A[0] - v.S[0] > 4*c.C*c.R + 2*v.alpha)
    # Lemma's statement's converse
    s.add(Or(
        v.A[-1] - v.S[-1] > v.A[0] - v.S[0] - v.alpha,
        v.c_f[0][-1] > 4*c.C*c.R + v.alpha))
    print("Proving that if queue is too big and cwnd is small enough, then "
          "queue will fall")
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # If cwnd < BDP - alpha and queue length < 4 BDP + 2 alpha, cwnd increases
    # by at-least alpha and queue length does not increase its bound
    c.T = 15
    c.compose = False  # we definitely need it to prove cwnd increases
    s, v = make_solver(c)
    # Lemma's assumption
    s.add(And(v.L[0] == 0, v.L[-1] == 0))
    s.add(v.alpha < (1 / 4) * c.C * c.R)
    s.add(v.c_f[0][dur] < c.C*c.R - v.alpha)
    s.add(v.A[0] - v.S[0] <= 4*c.C*c.R + 2*v.alpha)
    # Lemma's statement's converse
    s.add(Or(
        And(
            v.c_f[0][-1] < c.C*c.R - v.alpha,
            v.c_f[0][-1] < v.c_f[0][dur] + v.alpha),
        v.A[-1] - v.S[-1] > 4*c.C*c.R + 2*v.alpha))
    print("Proving that if cwnd is too small and the queue is small enough, "
          "cwnd increases")
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # If Copa has entered steady state, it does not leave it
    c.T = 10
    c.compose = False
    s, v = make_solver(c)
    ors = []
    # Lemma's assumption
    s.add(v.alpha < (1 / 7) * c.C * c.R)
    s.add(And(v.L[0] == 0, v.L[-1] == 0))
    s.add(v.c_f[0][dur] >= c.C*c.R - v.alpha)
    s.add(v.c_f[0][dur] <= 4*c.C*c.R + 2*v.alpha)
    s.add(v.A[0] - v.S[0] <= 4*c.C*c.R + 2*v.alpha)
    # Lemma's statement's converse
    ors.append(v.c_f[0][-1] > 4*c.C*c.R + v.alpha)
    ors.append(v.c_f[0][-1] < c.C*c.R - v.alpha)
    ors.append(v.A[-1] - v.S[-1] > 4*c.C*c.R + 2*v.alpha)
    s.add(Or(*ors))
    print("Proving that if Copa has entered steady state, it will "
          "remain there")
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")


if __name__ == "__main__":
    prove_steady_state()
