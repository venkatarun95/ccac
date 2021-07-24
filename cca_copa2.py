from config import ModelConfig
from variables import Variables
from my_solver import MySolver
from cache import run_query
from plot import plot_model
from utils import make_periodic


def cca_copa2(c: ModelConfig, s: MySolver, v: Variables):
    # Period over which we calculate cwnd
    per = c.R + 2 * c.D
    # The duration for which we let the cwnd etc. free
    dur = c.R + per

    for n in range(c.N):
        for t in range(c.T):
            if t < dur:
                # No constraints
                continue

            s.add(v.c_f[n][t] == v.S_f[n][t - c.R] - v.S_f[n][t - c.R - per] +
                  v.alpha)
            s.add(v.r_f[n][t] == c.C * 100)
