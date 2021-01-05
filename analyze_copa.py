import argparse
from typing import Optional
from z3 import And, Or, Real

from binary_search import BinarySearch, sat_to_val
from cache import run_query
from multi_flow import ModelConfig, freedom_duration, make_solver


def copa_steady_state(
    cfg: ModelConfig, err: float, timeout: float
):
    alpha_thresh = 0.1 * cfg.C * cfg.R
    q_thresh = 4 * cfg.C * cfg.R + 2 * Real("alpha")
    cwnd_thresh = 0.9 * cfg.C * cfg.R
    cwnd_thresh_u = 4 * cfg.C * cfg.R + 2 * Real("alpha")
    T = cfg.T

    dur = freedom_duration(cfg)

    # If queue < q_thresh and cwnd < cwnd_thresh, cwnd increases by at-least
    # alpha / 2
    s = make_solver(cfg)
    conds = []
    for n in range(cfg.N):
        s.add(Real(f"cwnd_{n},{dur-1}") <= cwnd_thresh)
        conds.append(Real(f"cwnd_{n},{T-1}")
                     < Real(f"cwnd_{n},{dur-1}") + Real("alpha") / 2)
    s.add(Or(*conds))
    s.add(Real(f"tot_inp_{dur-1}") - Real(f"tot_out_{dur-1}") <= q_thresh)
    s.add(Real("alpha") < alpha_thresh)
    qres = run_query(s, cfg, timeout=timeout)
    print("Cwnd increases:", qres.satisfiable)

    # If queue < q_thresh and cwnd < cwnd_thresh, queue never exceeds q_thresh
    s = make_solver(cfg)
    for n in range(cfg.N):
        s.add(Real(f"cwnd_{n},{dur-1}") <= cwnd_thresh)
    s.add(Real(f"tot_inp_{dur-1}") - Real(f"tot_out_{dur-1}") <= q_thresh)
    s.add(Real(f"tot_inp_{T-1}") - Real(f"tot_out_{T-1}") > q_thresh)
    s.add(Real("alpha") < alpha_thresh)
    qres = run_query(s, cfg, timeout=timeout)
    print("Queue remains small: ", qres.satisfiable)

    # If Copa makes it to the steady state, it stays there
    s = make_solver(cfg)
    conds = []
    for n in range(cfg.N):
        s.add(Real(f"cwnd_{n},{dur-1}") <= cwnd_thresh_u)
        s.add(Real(f"cwnd_{n},{dur-1}") >= cwnd_thresh)
        conds.append(Real(f"cwnd_{n},{T-1}") < cwnd_thresh)
        conds.append(Real(f"cwnd_{n},{T-1}") > cwnd_thresh_u)
        conds.append(
            Real(f"tot_inp_{T-1}") - Real(f"tot_out_{T-1}") > q_thresh)
    s.add(Real(f"tot_inp_{dur-1}") - Real(f"tot_out_{dur-1}") <= q_thresh)
    s.add(Real("alpha") < alpha_thresh)
    s.add(Or(*conds))
    qres = run_query(s, cfg, timeout=timeout)
    print("Stays there: ", qres.satisfiable)

    # If queue > q_thresh and cwnd <= cwnd_thresh_u, queue will fall by
    # at least alpha and cwnd never exceeds cwnd_thresh_u
    s = make_solver(cfg)
    conds = []
    for n in range(cfg.N):
        s.add(Real(f"cwnd_{n},{dur-1}") <= cwnd_thresh_u)
        conds.append(Real(f"cwnd_{n},{T-1}") > cwnd_thresh_u)
    conds.append(Real(f"tot_inp_{T-1}") - Real(f"tot_out_{T-1}")
                 >= Real("tot_inp_0") - Real("alpha"))
    s.add(Real(f"tot_inp_{dur-1}") - Real(f"tot_out_{dur-1}") > q_thresh)
    s.add(Or(*conds))
    s.add(Real("alpha") < alpha_thresh)
    qres = run_query(s, cfg, timeout=timeout)
    print("Queue always falls", qres.satisfiable)

    # If cwnd > cwnd_thresh_u, cwnd will fall by at-least alpha
    s = make_solver(cfg)
    conds = []
    for n in range(cfg.N):
        s.add(Real(f"cwnd_{n},{dur-1}") > cwnd_thresh_u)
        conds.append(Real(f"cwnd_{n},{T-1}")
                     >= Real(f"cwnd_{n},{dur-1}") - Real("alpha"))
    s.add(Or(*conds))
    s.add(Real("alpha") < alpha_thresh)
    qres = run_query(s, cfg, timeout=timeout)
    print("Cwnd always falls", qres.satisfiable)


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser(
        "steady_state", parents=[cfg_args, common_args])

    args = parser.parse_args()
    cfg = ModelConfig.from_argparse(args)

    if args.subcommand == "steady_state":
        bounds = copa_steady_state(cfg, args.err, args.timeout)
