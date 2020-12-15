import argparse
import pickle as pkl
from typing import Optional, Tuple
from z3 import And, Implies, Or, Real

from binary_search import BinarySearch
from cache import QueryResult, run_query
from multi_flow import ModelConfig, freedom_duration, make_solver, plot_model


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
        if qres.satisfiable == "sat":
            val = 3
        elif qres.satisfiable == "unknown":
            val = 2
        elif qres.satisfiable == "unsat":
            val = 1
        else:
            print(qres)
            assert(False)
        search.register_pt(pt, val)
    return search.get_bounds()


def find_cwnd_incr_bound(
    cfg: ModelConfig, max_cwnd: float, err: float, timeout: float
):
    ''' Finds a threshold such that, if the cwnd starts below this threshold,
    it would increase past that threshold at the end of the timeframe. Then
    finds a (possibly loose) bound on the minimum utilization it will
    eventually achieve. '''
    # In multiple of BDP
    cwnd_search = BinarySearch(0.01, max_cwnd, err)
    while True:
        pt = cwnd_search.next_pt()
        if pt is None:
            break
        thresh = pt * cfg.C * cfg.R

        s = make_solver(cfg)

        conds = []
        for n in range(cfg.N):
            for t in range(freedom_duration(cfg)):
                s.add(Real(f"cwnd_{n},{t}") <= thresh)
                # We need all the last freedom_duration(cfg) timesteps to be
                # large so we can apply induction to extend theorem to infinity
                for t1 in range(freedom_duration(cfg)):
                    conds.append(Real(f"cwnd_{n},{cfg.T-1-t}")
                                 < Real(f"cwnd_{n},{t}") + Real("alpha"))
        s.add(Or(*conds))

        print(f"Testing init cwnd = {pt} BDP")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            val = 3
        elif qres.satisfiable == "unknown":
            val = 2
        elif qres.satisfiable == "unsat":
            val = 1
        else:
            print(qres)
            assert(False)
        cwnd_search.register_pt(pt, val)

    # Find a (possibly loose) bound on achievable throughput
    thresh = cwnd_search.get_bounds()[0] * cfg.C * cfg.R
    util_search = BinarySearch(0, 1.0, err)
    while True:
        pt = util_search.next_pt()
        if pt is None:
            break

        s = make_solver(cfg)

        for n in range(cfg.N):
            for t in range(freedom_duration(cfg)):
                s.add(Real(f"cwnd_{n},{t}") >= thresh)

        s.add(Real(f"tot_out_{cfg.T-1}") < pt * cfg.C * (cfg.T - 1))

        print(f"Testing {pt * 100}% utilization")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            val = 3
        elif qres.satisfiable == "unknown":
            val = 2
        elif qres.satisfiable == "unsat":
            val = 1
        else:
            print(qres)
            assert(False)
        util_search.register_pt(pt, val)

    return (cwnd_search.get_bounds(), util_search.get_bounds())


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser("tpt_bound", parents=[cfg_args])
    tpt_bound_args.add_argument("--err", type=float, default=0.05)
    tpt_bound_args.add_argument("--timeout", type=float, default=10)

    cwnd_incr_bound_args = subparsers.add_parser("cwnd_incr_bound",
                                                 parents=[cfg_args])
    cwnd_incr_bound_args.add_argument("--err", type=float, default=0.05)
    cwnd_incr_bound_args.add_argument("--timeout", type=float, default=10)
    cwnd_incr_bound_args.add_argument(
        "--max_cwnd", type=float, default=5,
        help="As a multiple of BDP, the max cwnd threshold we should consider")

    plot_args = subparsers.add_parser("plot")
    plot_args.add_argument("cache_file_name")

    args = parser.parse_args()
    print(args)

    if args.subcommand == "tpt_bound":
        cfg = ModelConfig.from_argparse(args)
        bounds = find_lower_tpt_bound(
            cfg, args.err, args.timeout)
        print(bounds)
    elif args.subcommand == "cwnd_incr_bound":
        cfg = ModelConfig.from_argparse(args)
        bounds = find_cwnd_incr_bound(
            cfg, args.max_cwnd, args.err, args.timeout)
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
            assert(qres.model is not None)
            plot_model(qres.model, qres.cfg)
