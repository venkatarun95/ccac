from config import ModelConfig
from model import make_solver

if __name__ == "__main__":
    from abr import make_abr_periodic
    from cache import run_query
    from plot import plot_model
    from utils import make_periodic

    c = ModelConfig(N=1,
                    D=1,
                    R=1,
                    T=10,
                    C=1,
                    buf_min=5,
                    buf_max=5,
                    dupacks=None,
                    cca="aimd",
                    compose=True,
                    alpha=None,
                    pacing=False,
                    epsilon="zero",
                    unsat_core=True,
                    simplify=False,
                    app="bb_abr")

    s, v = make_solver(c)
    dur = c.R + c.R + 2 * c.D
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    s.add(v.av[0].chunk_time < c.T / 3)
    s.add(v.alpha < 2)
    s.add(v.av[0].chunk_time > 1.5)
    s.add(v.av[0].Ch_s[0] > 1.5)

    make_abr_periodic(c.ac[0], v.av[0], c, s, v)
    make_periodic(c, s, v, dur)
    qres = run_query(s, c)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)
