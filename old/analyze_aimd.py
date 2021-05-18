import argparse
import matplotlib.pyplot as plt
import numpy as np
from z3 import And, If, Or, Real

from binary_search import BinarySearch
from cache import run_query
from questions import find_bound, find_cwnd_incr_bound,\
    find_const_cwnd_util_lbound, find_periodic_low_cwnd
from multi_flow import ModelConfig, make_solver, freedom_duration
from my_solver import MySolver

# In units of 1 BDP
# buf_sizes = np.asarray(
#     list(np.linspace(0.1, 1.1, 5)) + list(np.linspace(1.1, 3.1, 6)))
# buf_sizes = [0.1, 0.5, 1, 1.1, 1.45, 1.5, 2, 2.25, 2.5, 2.75, 3]
# buf_sizes = [0.1, 0.9, 1.3, 1.6, 1.7, 2, 3]
buf_sizes = [1.9]
# buf_sizes = [0.1, 0.25, 0.5, 0.75, 0.9, 1, 1.1, 1.15, 1.2, 1.25, 1.5, 1.75,
#             1.9, 2, 2.1, 2.25, 2.5, 2.75, 3, 3.5, 4]


def loss_thresh(cfg: ModelConfig, err: float, timeout: float):
    global buf_sizes
    assert(cfg.N == 1)
    buf_sizes = np.asarray(buf_sizes) * (cfg.C * cfg.R)
    max_gap = Real("alpha") + cfg.C * (cfg.R + cfg.D)

    def max_cwnd_f(cfg: ModelConfig):
        return cfg.C*(cfg.R + cfg.D) + cfg.buf_min  # + 2 * Real("alpha")

    def gap(t: int, cfg: ModelConfig):
        return Real(f"tot_lost_{t}") - Real(f"loss_detected_0,{t}")

    def test(cfg: ModelConfig, thresh: float):
        max_cwnd = max_cwnd_f(cfg)
        s = make_solver(cfg)
        s.add(Or(*[
            And(
                Real(f"tot_lost_{t}") > Real(f"tot_lost_{t-1}"),
                Real(f"cwnd_0,{t}") < thresh,
                # Real(f"tot_lost_{t-1}") == 0
            )
            for t in range(3, cfg.T)
        ]))
        # s.add(Real("tot_lost_3") == 0)
        # s.add(gap(0, cfg) == 0)

        s.add(gap(0, cfg) <= max_gap)
        s.add(Real("cwnd_0,0") < max_cwnd)

        s.add(Real("alpha") < 0.1 * cfg.C * cfg.R)
        # s.add(Real("alpha") < cfg.buf_min / 2)
        return s

    T_orig = cfg.T
    cwnd_threshes = []
    for buf_size in buf_sizes:
        cfg.buf_max = buf_size
        cfg.buf_min = buf_size
        max_cwnd = max_cwnd_f(cfg)
        cfg.T = T_orig

        if buf_size >= 2 * cfg.C * cfg.R:
            cfg.T = 15

        print(f"Testing buffer size {buf_size}")

        # If cwnd > max_cwnd, it will fall
        s = make_solver(cfg)
        s.add(Real("tot_lost_0") == Real(f"tot_lost_{cfg.T-1}"))
        s.add(Real(f"cwnd_0,{cfg.T-1}") > max_cwnd)
        # Eliminate timeouts where we just stop sending packets
        for t in range(cfg.T):
            s.add(Real(f"tot_inp_{t}") - Real(f"tot_lost_{t}")
                  > Real(f"tot_out_{t}"))
        s.add(Real("alpha") < 0.1 * cfg.C * cfg.R)
        # qres = run_query(s, cfg, timeout)
        # print("tested max cwnd: ", qres.satisfiable)
        # assert(qres.satisfiable == "unsat")

        # If cwnd < max_cwnd, it will stay there
        s = make_solver(cfg)
        s.add(Real("cwnd_0,0") < max_cwnd)
        s.add(Real(f"cwnd_0,{cfg.T-1}") > max_cwnd)
        s.add(Real("alpha") < 0.1 * cfg.C * cfg.R)
        # qres = run_query(s, cfg, timeout)
        # print("Tested max cwnd stay: ", qres.satisfiable)
        # assert(qres.satisfiable == "unsat")

        # If gap > max_gap, it will fall by at-least C
        s = make_solver(cfg)
        s.add(gap(cfg.T-1, cfg) > max_gap)
        s.add(gap(0, cfg) - cfg.C < gap(cfg.T-1, cfg))
        for t in range(cfg.T):
            s.add(Real(f"cwnd_0,{t}") < max_cwnd)
            # Eliminate timeouts where we just stop sending packets
            s.add(Real(f"tot_inp_{t}") - Real(f"tot_lost_{t}")
                  > Real(f"tot_out_{t}"))
        # s.add(Real("alpha") < cfg.C * cfg.R * 0.1)
        # qres = run_query(s, cfg, timeout)
        # print("Tested loss detect: ", qres.satisfiable)
        # assert(qres.satisfiable == "unsat")

        s = make_solver(cfg)
        s.add(gap(0, cfg) < max_gap)
        s.add(gap(cfg.T-1, cfg) >= max_gap)
        s.add(Real("alpha") < 0.1 * cfg.C * cfg.R)
        for t in range(cfg.T):
            # Eliminate timeouts where we just stop sending packets
            s.add(Real(f"tot_inp_{t}") - Real(f"tot_lost_{t}")
                  > Real(f"tot_out_{t}"))
        # qres = run_query(s, cfg, timeout)
        # print("Tested gap remains low: ", qres.satisfiable)
        # assert(qres.satisfiable == "unsat")

        if True:
            # cfg.T = 5
            if buf_size <= cfg.C * (cfg.R + cfg.D):
                thresh = buf_size - Real("alpha")
            else:
                thresh = buf_size + cfg.C * (cfg.R - 1) - Real("alpha")
            s = test(cfg, thresh)
            qres = run_query(s, cfg, timeout)
            print("Tested loss threshold: ", qres.satisfiable)
            assert(qres.satisfiable == "unsat")

            s = test(cfg, thresh + 0.1)
            qres = run_query(s, cfg, timeout)
            print("Tested loss threshold + 0.1: ", qres.satisfiable)
            assert(qres.satisfiable == "sat")
            continue

        cwnd_thresh = find_bound(test, cfg,
                                 BinarySearch(0, max_cwnd, err), timeout)
        print(cwnd_thresh)
        cwnd_threshes.append(cwnd_thresh)
    print(list(buf_sizes), cwnd_threshes)


def single_flow_util(
    cfg: ModelConfig, err: float, timeout: float
):
    ''' Find a steady-state such that if it enters steady state, it will remain
    there '''
    global buf_sizes
    buf_sizes = buf_sizes / (cfg.C * cfg.R)

    def cwnd_stay_bound(cfg: ModelConfig, thresh: float) -> MySolver:
        s = make_solver(cfg)
        conds = []
        dur = freedom_duration(cfg)
        for n in range(cfg.N):
            for t in range(dur):
                s.add(Real(f"cwnd_{n},{t}") >= thresh)
            for t in range(dur, cfg.T):
                # We need all the last freedom_duration(cfg) timesteps to be
                # large so we can apply induction to extend theorem to infinity
                conds.append(Real(f"cwnd_{n},{t}") < thresh)
        s.add(Or(*conds))
        assert(cfg.N == 1)
        s.add(Real("tot_inp_0") - Real("tot_lost_0") - (0-Real("wasted_0"))
              <= Real("cwnd_0,0") - cfg.C*cfg.R)
        return s

    # Plot as a function of buffer size (droptail)
    cwnd_bounds = []
    util_bounds = []
    T = cfg.T

    for buf_size in np.asarray(buf_sizes) * cfg.C * cfg.R:
        cfg.buf_min = buf_size
        cfg.buf_max = buf_size

        # Queue size will eventually match cwnd. We use this in
        # cwnd_stay_bound to make it tighter
        assert(cfg.N == 1)
        s = make_solver(cfg)
        s.add(Real("cwnd_0,0") < cfg.C * cfg.R + buf_size)
        q_bound = Real(f"cwnd_0,{T-1}") - cfg.C*cfg.R
        q_bound = If(q_bound >= 0, q_bound, 0)
        s.add(Real(f"tot_inp_{T-1}") - Real(f"tot_lost_{T-1}")
              - (cfg.C*(T-1) - Real(f"wasted_{T-1}"))
              > q_bound)
        # Loss did not happen recently
        s.add(Real(f"cwnd_0,{T-1}") > Real(f"cwnd_0,{T-2}"))
        qres = run_query(s, cfg, timeout=timeout)
        print("Queue will eventually be cwnd limited", qres.satisfiable)
        assert(qres.satisfiable == "unsat")

        incr_bound = find_cwnd_incr_bound(cfg, None, err, timeout)
        print(f"For buffer size {buf_size} incr_bound={incr_bound}")

        max_cwnd = cfg.C * cfg.R + cfg.buf_max

        # Same as find_cwnd_stay_bound
        print(f"Testing init cwnd for stay = {incr_bound[0]} BDP")
        s = cwnd_stay_bound(cfg, incr_bound[0])
        qres = run_query(s, cfg, timeout=timeout)
        print(qres.satisfiable)

        if qres.satisfiable != "unsat":
            print("Could not prove bound. Will search for a new stay bound")
            stay_bound = find_bound(cwnd_stay_bound, cfg,
                                    BinarySearch(0, max_cwnd, err), timeout)
            if stay_bound[0] > incr_bound[0]:
                print("Failed to prove any bounds: ", stay_bound)
                return
            bound = stay_bound[0]
        else:
            # This is the definitive bound
            bound = incr_bound[0]

        # This is a definitive bound
        cwnd_thresh = bound
        #util_bound = find_const_cwnd_util_lbound(
        #    cfg, cwnd_thresh, err, timeout)
        util_bound = [0]
        print(f"For buffer size {buf_size} util_bound={util_bound}")

        cwnd_bounds.append(cwnd_thresh)
        util_bounds.append(util_bound[0] * 100)

    print([x for x in zip(buf_sizes, cwnd_bounds, util_bounds)])

    fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
    ax1.plot(buf_sizes, cwnd_bounds)
    ax2.plot(buf_sizes, util_bounds)
    ax1.set_ylabel("Steady state cwnd (in BDP)")
    ax2.set_ylabel("Minimum utilization %")
    ax2.set_xlabel("Buffer size (in BDP)")
    plt.show()
    plt.savefig("/tmp/single_flow_util.svg")
    print(buf_sizes, cwnd_bounds, util_bounds)


def plot_periodic_low_util(
    cfg: ModelConfig, err: float, timeout: float
):
    global buf_sizes
    assert(cfg.N == 1)
    buf_sizes = np.asarray(buf_sizes) * cfg.C * cfg.R

    def model_cons(cfg: ModelConfig, thresh: float):
        dur = cfg.R
        s = make_solver(cfg)

        for t in range(dur):
            t0 = t+cfg.T-dur
            s.add(Real(f"losts_0,{t}") - Real(f"loss_detected_0,{t}")
                  == Real(f"losts_0,{t0}") - Real(f"loss_detected_0,{t0}"))
            s.add(Real(f"inp_0,{t}") - Real(f"losts_0,{t}") - Real(f"out_0,{t}")
                  == Real(f"inp_0,{t0}") - Real(f"losts_0,{t0}") - Real(f"out_0,{t0}"))
            s.add(cfg.C*t - Real(f"wasted_{t}") - Real(f"out_0,{t}")
                  == cfg.C*t0 - Real(f"wasted_{t0}") - Real(f"out_0,{t0}"))
            s.add(Real(f"losts_0,{t}") - Real(f"loss_detected_0,{t}")
                  == Real(f"losts_0,{t0}") - Real(f"loss_detected_0,{t0}"))
        s.add(Real(f"tot_out_{cfg.T-1}") - Real("tot_out_0")
              < thresh * cfg.C * (cfg.T - 1))
        s.add(Real("cwnd_0,0") == Real(f"cwnd_0,{cfg.T-1}"))

        # Eliminate timeouts where we just stop sending packets
        for t in range(cfg.T):
            s.add(Real(f"tot_inp_{t}") - Real(f"tot_lost_{t}")
                  > Real(f"tot_out_{t}"))

        return s

    cwnd_bounds = []
    for buf_size in buf_sizes:
        cfg.buf_min = buf_size
        cfg.buf_max = buf_size

        bound = find_bound(model_cons, cfg, BinarySearch(0, 1, err), timeout)
        print(f"Util bound {bound}")
        cwnd_bounds.append(bound)

    print([x for x in zip(buf_sizes, cwnd_bounds)])
    fig, ax = plt.subplots(1, 1)
    ax.plot(buf_sizes, cwnd_bounds)
    ax.set_ylabel("Steady state cwnd (in BDP)")
    ax.set_xlabel("Buffer size (in BDP)")
    plt.show()


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser(
        "loss_thresh", parents=[cfg_args, common_args])

    tpt_bound_args = subparsers.add_parser(
        "single_flow_util", parents=[cfg_args, common_args])

    tpt_bound_args = subparsers.add_parser(
        "plot_periodic_low_util", parents=[cfg_args, common_args])

    args = parser.parse_args()
    cfg = ModelConfig.from_argparse(args)

    if args.subcommand == "loss_thresh":
        loss_thresh(cfg, args.err, args.timeout)
    elif args.subcommand == "single_flow_util":
        single_flow_util(cfg, args.err, args.timeout)
    elif args.subcommand == "plot_periodic_low_util":
        plot_periodic_low_util(cfg, args.err, args.timeout)
    else:
        print(f"Unrecognized command '{args.subcommand}'")
