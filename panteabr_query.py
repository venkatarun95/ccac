from abr import App
from config import ModelConfig
from model import make_solver
from my_solver import MySolver
from variables import Variables


if __name__ == "__main__":
    from cache import run_query
    from plot import plot_model
    from utils import make_periodic

    c = ModelConfig(N=1,
                    D=1,
                    R=1,
                    T=10,
                    C=1,
                    buf_min=None,
                    buf_max=None,
                    dupacks=None,
                    cca="rocc",
                    compose=True,
                    alpha=None,
                    pacing=False,
                    epsilon="zero",
                    unsat_core=False,
                    simplify=False,
                    app="panteabr")

    s, v = make_solver(c)
    # dur = v.cv.dur
    # Consider the no loss case for simplicity
    s.add(v.alpha < 2)
    s.add(v.L[0] == 0)

    # Query: Low throughput
    if False:
        s.add(v.A_f[0][0] == v.c_f[0][0])
        s.add(v.c_f[0][-1] < v.c_f[0][5])
        s.add(v.S[-1] - v.S[5] <= 0.1 * c.C * (c.T - 5))

    # Query: Does dummy dominate?
    elif True:
        s.add(v.av[0].actually_sent[-1] - v.av[0].actually_sent[5] <= 0.8 * (v.A[-1] - v.A[5]))

    qres = run_query(s, c, timeout=1200)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)
