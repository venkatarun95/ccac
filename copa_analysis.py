from z3 import Real

from cache import run_query
from multi_flow import ModelConfig, make_solver, model_to_dict, plot_model


def lower_tpt_bound():
    cfg = ModelConfig(
        N=1,
        D=1,
        R=2,
        T=10,
        C=5,
        buf_min=None,
        dupacks=0.125,
        cca="copa",
        compose=False,
        alpha=1.0)

    # Do a binary search over tpt
    s = make_solver(cfg)

    # If cwnd decreased in the duration, we are sort of in equilibrium
    for t in range(cfg.R + cfg.D):
        s.add(Real("cwnd_0,%d" % t) >= Real("cwnd_0,%d" % (cfg.T-1)))

    s.add(Real("tot_out_%d" % (cfg.T - 1)) < cfg.C * cfg.T / 2)

    # Run the model
    qres = run_query(s)
    print(qres.satisfiable)
    if str(qres.satisfiable) != 'sat':
        exit()

    plot_model(qres.model, cfg)


lower_tpt_bound()
