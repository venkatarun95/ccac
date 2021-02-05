import argparse
import pickle as pkl
from typing import Callable, Optional, Tuple
from z3 import And, Or, Real, Solver

from binary_search import BinarySearch, sat_to_val
from cache import QueryResult, run_query
from multi_flow import ModelConfig, freedom_duration, make_solver, plot_model


def find_bound(model_cons: Callable[[ModelConfig, float], Solver],
               cfg: ModelConfig, search: BinarySearch, timeout: float,
               reverse: bool = False):
    while True:
        thresh = search.next_pt()
        if thresh is None:
            break
        s = model_cons(cfg, thresh)

        print(f"Testing threshold = {thresh}")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(thresh, sat_to_val(qres.satisfiable, reverse))
    return search.get_bounds()


def find_lower_tpt_bound(
    cfg: ModelConfig, err: float, timeout: float
) -> Tuple[float, Optional[Tuple[float, float]], float]:
    ''' Finds a bound in terms of percentage used '''
    search = BinarySearch(0.0, 1.0, err)
    while True:
        pt = search.next_pt()
        if pt is None:
            break

        s = make_solver(cfg)

        # Add constraints that allow us to extend this finite time result to
        # infinity via induction.

        # We start at timestep 1, so inp and out can have any value in the
        # beginning

        # Rate is high at some point in the future. We use from 0 to t (and not
        # 1 to t-1 or 0 to t+1) because both 0 to 1 is already required to have
        # a high rate, so our bound can exploit that. required to have a high
        # rate.

        # We do not take this idea further and pick 0 to t+1 because after
        # induction we say that we have a sequence of *non-overlapping*
        # intervals with a high rate, therefore the whole period also has a
        # high rate. This doesn't work if the intervals overlap, since the
        # overlapping portion could have a very high rate which will be double
        # counted.
        proven_cond = []
        for t in range(2, cfg.T):
            proven_cond.append(
                Or(
                    Real("tot_out_%d" % (t + 1)) - Real("tot_out_%d" % t)
                    <= cfg.C*pt,
                    Real("tot_out_%d" % t)-Real("tot_out_1") <= cfg.C*(t-1)*pt
                )
            )
        s.add(And(
            Real("tot_out_2") - Real("tot_out_1") >= cfg.C * pt,
            And(*proven_cond)
        ))

        # Utilization
        s.add(Real("tot_out_%d" % (cfg.T - 1)) < cfg.C * (cfg.T - 1) * pt)

        print(f"Testing {pt * 100}% utilization")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(pt, sat_to_val(qres.satisfiable))
    return search.get_bounds()


def find_const_cwnd_util_lbound(
    cfg: ModelConfig, cwnd_thresh: float, err: float, timeout: float
):
    ''' Find a (possibly loose) bound on the minimum utilization it will
    eventially achieve if initial cwnds are all greater than given threshold.
    '''

    search = BinarySearch(0, 1.0, err)
    while True:
        pt = search.next_pt()
        if pt is None:
            break

        s = make_solver(cfg)

        for n in range(cfg.N):
            for t in range(freedom_duration(cfg)):
                s.add(Real(f"cwnd_{n},{t}") >= cwnd_thresh)

        s.add(Real(f"tot_out_{cfg.T-1}") < pt * cfg.C * (cfg.T - 1))

        print(f"Testing {pt * 100}% utilization")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(pt, sat_to_val(qres.satisfiable))
    return search.get_bounds()


def find_cwnd_incr_bound(
    cfg: ModelConfig, max_cwnd: Optional[float], err: float, timeout: float
):
    ''' Find a threshold such that, if the cwnd starts below this threshold, it
    would increase past that threshold at the end of the timeframe. Then
    invoke find_const_cwnd_util_lbound. '''
    if max_cwnd is None:
        if cfg.buf_max is None:
            print("Error: Neither max_cwnd nor buf_max are specified")
            return
        max_cwnd = cfg.C * cfg.R + cfg.buf_max
    # In multiple of BDP
    search = BinarySearch(0.01, max_cwnd, err)
    while True:
        thresh = search.next_pt()
        if thresh is None:
            break

        s = make_solver(cfg)

        conds = []
        dur = freedom_duration(cfg)
        for n in range(cfg.N):
            for t in range(dur):
                s.add(Real(f"cwnd_{n},{t}") <= thresh)
                # We need all the last freedom_duration(cfg) timesteps to be
                # large so we can apply induction to extend theorem to infinity
                conds.append(And(
                    Real(f"cwnd_{n},{cfg.T-1-t}")
                    < Real(f"cwnd_{n},{dur-1}") + Real("alpha"),
                    Real(f"cwnd_{n},{cfg.T-1-t}") < thresh))
        s.add(Or(*conds))

        print(f"Testing init cwnd = {thresh}")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(thresh, sat_to_val(qres.satisfiable))

    return search.get_bounds()


def cwnd_stay_bound(cfg: ModelConfig, thresh: float) -> Solver:
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
    return s


def find_periodic_low_util(
    cfg: ModelConfig, no_loss: bool, err: float, timeout: float,
):
    T = cfg.T

    search = BinarySearch(0, 1, err)
    while True:
        util = search.next_pt()
        if util is None:
            break

        s = make_solver(cfg)

        # Make sure everything is periodic
        dur = freedom_duration(cfg)
        for n in range(cfg.N):
            for t in range(dur):
                tf = cfg.T-dur+t
                s.add(Real(f"cwnd_{n},{t}") == Real(f"cwnd_{n},{tf}"))

            s.add(Real(f"inp_{n},0") - Real(f"out_{n},0")
                  == Real(f"inp_{n},{T-1}") - Real(f"out_{n},{T-1}"))
            s.add(Real(f"losts_{n},0") - Real(f"loss_detected_{n},0")
                  == Real(f"losts_{n},{T-1}") - Real(f"loss_detected_{n},{T-1}"))

            if no_loss:
                s.add(Real(f"losts_{n},0") == 0)
        s.add(Real(f"tot_out_{cfg.T-1}") < util * cfg.C * (T - 1))

        # Eliminate timeouts where we just stop sending packets
        for t in range(cfg.T):
            s.add(Real(f"tot_inp_{t}") - Real(f"tot_lost_{t}")
                  > Real(f"tot_out_{t}"))

        print(f"Testing {util * 100}% utilization")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(util, sat_to_val(qres.satisfiable))
    return search.get_bounds()


def find_periodic_low_cwnd(
    cfg: ModelConfig, no_loss: bool, err: float, timeout: float
):
    T = cfg.T

    search = BinarySearch(0, cfg.C * T + cfg.buf_max, err)
    while True:
        thresh = search.next_pt()
        if thresh is None:
            break

        s = make_solver(cfg)

        # Make sure everything is periodic
        dur = freedom_duration(cfg)
        for n in range(cfg.N):
            for t in range(dur):
                tf = cfg.T-dur+t
                s.add(Real(f"cwnd_{n},{t}") == Real(f"cwnd_{n},{tf}"))

            s.add(Real(f"inp_{n},0") - Real(f"losts_{n},0") - Real(f"out_{n},0")
                  == Real(f"inp_{n},{T-1}") - Real(f"losts_{n},{T-1}") - Real(f"out_{n},{T-1}"))
            s.add(Real(f"losts_{n},0") - Real(f"loss_detected_{n},0")
                  == Real(f"losts_{n},{T-1}") - Real(f"loss_detected_{n},{T-1}"))

            if no_loss:
                s.add(Real(f"losts_{n},0") == 0)

            s.add(Or(*[Real(f"cwnd_{n},{t}") < thresh for t in range(T)]))

        s.add(Real("tot_out_0") - (-Real("wasted_0"))
              == Real(f"tot_out_{T-1}") - (cfg.C * (T-1) - Real(f"wasted_{T-1}")))

        print(f"Testing cwnd thresh {thresh / (cfg.C * cfg.R)} BDP")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(thresh, sat_to_val(qres.satisfiable))
    return search.get_bounds()


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser(
        "tpt_bound", parents=[cfg_args, common_args])

    cwnd_incr_bound_args = subparsers.add_parser(
        "cwnd_incr_bound",
        parents=[cfg_args, common_args])
    cwnd_incr_bound_args.add_argument(
        "--max-cwnd", type=float, required=False,
        help="As a multiple of BDP, the max cwnd threshold we should consider")

    cwnd_stay_bound_args = subparsers.add_parser(
        "cwnd_stay_bound",
        parents=[cfg_args, common_args])
    cwnd_stay_bound_args.add_argument(
        "--max-cwnd", type=float, required=False,
        help="As a multiple of BDP, the max cwnd threshold we should consider")

    const_cwnd_util_lbound_args = subparsers.add_parser(
        "const_cwnd_util_lbound",
        parents=[cfg_args, common_args])
    const_cwnd_util_lbound_args.add_argument(
        "--cwnd-thresh", type=float, required=True)

    periodic_low_util_args = subparsers.add_parser(
        "periodic_low_util",
        parents=[cfg_args, common_args])
    periodic_low_util_args.add_argument("--no-loss", action="store_const",
                                        const=True, default=False)

    periodic_low_cwnd_args = subparsers.add_parser(
        "periodic_low_cwnd",
        parents=[cfg_args, common_args])
    periodic_low_cwnd_args.add_argument("--no-loss", action="store_const",
                                        const=True, default=False)

    plot_args = subparsers.add_parser("plot")
    plot_args.add_argument("cache_file_name")

    args = parser.parse_args()
    if args.subcommand != "plot":
        cfg = ModelConfig.from_argparse(args)

    if args.subcommand == "tpt_bound":
        bounds = find_lower_tpt_bound(
            cfg, args.err, args.timeout)
        print(bounds)
    elif args.subcommand == "cwnd_incr_bound":
        bounds = find_cwnd_incr_bound(
            cfg, args.max_cwnd, args.err, args.timeout)
        print(bounds)
    elif args.subcommand == "cwnd_stay_bound":
        bounds = find_bound(cwnd_stay_bound, cfg,
                            BinarySearch(0, cfg.C*cfg.R+cfg.buf_max, args.err),
                            args.timeout)
        print(bounds)
    elif args.subcommand == "const_cwnd_util_lbound":
        bounds = find_const_cwnd_util_lbound(
            cfg, args.cwnd_thresh, args.err, args.timeout)
        print(bounds)
    elif args.subcommand == "periodic_low_util":
        bounds = find_periodic_low_util(
            cfg, args.no_loss, args.err, args.timeout)
        print(bounds)
    elif args.subcommand == "periodic_low_cwnd":
        bounds = find_periodic_low_cwnd(
            cfg, args.no_loss, args.err, args.timeout)
        print(bounds)
    elif args.subcommand == "plot":
        try:
            f = open(args.cache_file_name, 'rb')
            qres: QueryResult = pkl.load(f)
        except Exception as e:
            print("Exception while loacing cached file")
            print(e)
        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            print(qres)
            assert(qres.model is not None)
            plot_model(qres.model, qres.cfg)
