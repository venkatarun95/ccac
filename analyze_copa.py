import argparse
from typing import Optional
from z3 import And, Or, Real

from binary_search import BinarySearch, sat_to_val
from cache import run_query
from multi_flow import ModelConfig, freedom_duration, make_solver


def copa_steady_state(
    cfg: ModelConfig, err: float, timeout: float
):
    alpha_thresh = 0.1
    q_thresh_l = 3

    dur = freedom_duration(cfg)

    # Find cwnd_thresh s.t. if initial cwnd is below it and initial queue is
    # below q_thresh_l, cwnd will increase
    search = BinarySearch(0.01, 2, err)
    while True:
        pt = search.next_pt()
        if pt is None:
            break
        thresh = pt * cfg.C * cfg.R

        s = make_solver(cfg)

        conds = []
        for n in range(cfg.N):
            for t in range(dur):
                s.add(Real(f"cwnd_{n},{t}") <= thresh)
                # We need all the last freedom_duration(cfg) timesteps to be
                # large so we can apply induction to extend theorem to infinity

                # If we add alpha, we get an uninteresting case. Hence we use
                # alpha / 2. All we need here is any number > 0
                conds.append(Real(f"cwnd_{n},{cfg.T-1-t}")
                             < Real(f"cwnd_{n},{dur-1}") + Real("alpha") / 2)
        s.add(Or(*conds))

        # Queue has to be small to begin with
        s.add(Real("tot_inp_0") <= q_thresh_l * cfg.C * cfg.R)
        s.add(Real("alpha") < alpha_thresh)

        print(f"Testing init cwnd = {pt} BDP")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(pt, sat_to_val(qres.satisfiable))

    cwnd_thresh = search.get_bounds()[0]
    # cwnd_thresh = 0.9 * cfg.C * cfg.R
    print(search.get_bounds())
    print(f"Lower cwnd threshold = {cwnd_thresh} BDP")

    # Find q_thresh_u s.t. if queue starts above q_thresh_u, it will drop
    search = BinarySearch(0.1, 10, err)
    while True:
        pt = search.next_pt()
        if pt is None:
            break
        q_thresh = pt * cfg.C * cfg.R

        s = make_solver(cfg)
        for t in range(dur):
            # Depending on alpha upto 0.5 BDP, this constant is between 3 to 5
            s.add(Real(f"tot_inp_{t}") > q_thresh)
            s.add(Real(f"tot_inp_{cfg.T-1}") - Real(f"tot_out_{cfg.T-1}")
                  >= Real(f"tot_inp_{t}"))
            # s.add(Real(f"tot_inp_{cfg.T-1}") - Real(f"tot_out_{cfg.T-1}")
            #       >= 3 * cfg.C * cfg.D + 4 * Real("alpha"))

        s.add(Real("alpha") < alpha_thresh)

        print(f"Testing upper queue threshold = {q_thresh}")
        qres = run_query(s, cfg, timeout=timeout)
        print(qres.satisfiable)
        search.register_pt(pt, sat_to_val(qres.satisfiable))
    q_thresh_u = search.get_bounds()[0]
    q_thresh_u = 5
    print(f"Upper queue threshold = {q_thresh_u} BDP")

    # Prove that if initial cwnd >= cwnd_thresh and initial queue <= q_thresh_l,
    # cwnd will either remain high or queue exceeds q_thresh_u
    s = make_solver(cfg)
    conds = []
    for t in range(dur):
        for n in range(cfg.N):
            s.add(Real(f"cwnd_{n},{t}") >= cwnd_thresh)
            conds.append(Real(f"cwnd_{n},{cfg.T-1}") < cwnd_thresh)
        s.add(Real(f"tot_inp_{t}") <= q_thresh_l * cfg.C * cfg.R)
    s.add(Or(And(*conds),
             Real(f"tot_inp_{cfg.T-1}") - Real(f"tot_out_{cfg.T-1}")
             > q_thresh_u * cfg.C * cfg.R))
    # s.add(And(*conds))
    print("Condition:", qres.satisfiable)

    # Find bound on utilization if initial cwnd >= cwnd_thresh and initial queue
    # <= q_thresh_u
    search = BinarySearch(0, 1, err)
    while True:
        pt = search.next_pt()
        if pt is None:
            break
        s = make_solver(cfg)
        conds = []
        for t in range(dur):
            for n in range(cfg.N):
                s.add(Real(f"cwnd_{n},{t}") >= cwnd_thresh)
            s.add(Real(f"tot_inp_{t}") <= q_thresh_u * cfg.C * cfg.R)
        s.add(Real("alpha") < alpha_thresh)
        s.add(Real(f"tot_out_{cfg.T-1}") < pt * cfg.C * (cfg.T - 1))

        qres = run_query(s, cfg, timeout=timeout)
        print(qres.satisfiable)
        search.register_pt(pt, sat_to_val(qres.satisfiable))
    print(f"Utilization bound: {search.get_bounds()}")


    # If cwnd greater than BDP + alpha * thresh, we decrease
    # search = BinarySearch(0.5, 64, err)
    # while True:
    #     pt = search.next_pt()
    #     if pt is None:
    #         break
    #     thresh = 0.8 * cfg.C * cfg.R # + Real("alpha") * pt
    #
    #     s = make_solver(cfg)
    #
    #     conds = []
    #     dur = freedom_duration(cfg)
    #     for n in range(cfg.N):
    #         for t in range(dur):
    #             s.add(Real(f"cwnd_{n},{t}") <= thresh)
    #             # We need all the last freedom_duration(cfg) timesteps to be
    #             # large so we can apply induction to extend theorem to infinity
    #             conds.append(Real(f"cwnd_{n},{cfg.T-1-t}")
    #                          <= Real(f"cwnd_{n},{dur-1}"))
    #     s.add(Or(*conds))
    #     # s.add(Real("tot_inp_0") == 0)
    #     #s.add(Real(f"tot_out_{cfg.T-1}") < 0.44 * cfg.C * (cfg.T - 1))
    #
    #     print(f"Testing init cwnd = BDP + {pt} * alpha")
    #     qres = run_query(s, cfg, timeout=timeout)
    #
    #     print(qres.satisfiable)
    #     search.register_pt(pt, sat_to_val(qres.satisfiable, reverse=True))

    # return search.get_bounds()


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
        print(bounds)
