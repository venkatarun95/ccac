import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import pickle as pkl
import sys
from fractions import Fraction
from typing import List, Optional, Tuple

from .cache import QueryResult
from .config import ModelConfig
from .utils import ModelDict


def generate_incal_trace(m: ModelDict, cfg: ModelConfig):
    def to_arr(name: str) -> np.array:
        names = [f"{name}_{t}" for t in range(cfg.T)]
        res = []
        t = 0
        for n in names:
            if n in m:
                res.append(m[n])
            else:
                # Used only to generate values for bwdth * t
                res.append(Fraction(cfg.C * t))
                t += 1
        return np.array(res)

    variable_names: list[str] = ["tot_arrival", "tot_service", "wasted", "tot_lost", "token_gen"]
    for var in variable_names:
        values = list(map(lambda x: "fractions.{}".format(repr(x)), to_arr(var)))
        assignment = ", ".join(values)
        print(
            'variable_dict["{}"]: [{}],'.format(var, assignment)
        )


def plot_model(m: ModelDict, cfg: ModelConfig):
    def to_arr(name: str, n: Optional[int] = None, frac=False) -> np.array:
        if n is None:
            names = [f"{name}_{t}" for t in range(cfg.T)]
        else:
            names = [f"{name}_{n},{t}" for t in range(cfg.T)]
        res = []
        for n in names:
            if n in m:
                res.append(m[n])
            else:
                res.append(-1)
        if frac:
            return res
        return np.array(res)

    # Print the constants we picked
    if cfg.dupacks is None:
        print("dupacks = ", m["dupacks"])
    if cfg.cca in ["aimd", "fixed_d", "copa"] and cfg.alpha is None:
        print("alpha = ", m["alpha"])
    if not cfg.compose:
        print("epsilon = ", m["epsilon"])

    # Configure the plotting
    fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
    fig.set_size_inches(18.5, 10.5)
    ax1.grid(True)
    ax2.grid(True)
    ax2.set_xticks(range(0, cfg.T))
    ax2.yaxis.set_major_locator(matplotlib.ticker.MaxNLocator(integer=True))

    # Create 3 y-axes in the second plot
    ax2_rtt = ax2.twinx()
    ax2_rate = ax2.twinx()
    ax2.set_ylabel("Cwnd")
    ax2.set_xlabel("Time")
    ax2_rtt.set_ylabel("Q Delay")
    ax2_rate.set_ylabel("Rate")
    ax2_rate.spines["right"].set_position(("axes", 1.05))
    ax2_rate.spines["right"].set_visible(True)

    linestyles = ['--', ':', '-.', '-']
    adj = 0  # np.asarray([C * t for t in range(T)])
    times = [t for t in range(cfg.T)]
    ct = np.asarray([cfg.C * t for t in range(cfg.T)])

    ax1.plot(times, ct - to_arr("wasted"),
             color='black', marker='o', label='Bound', linewidth=3)
    ax1.plot(times[cfg.D:], (ct - to_arr("wasted"))[:-cfg.D],
             color='black', marker='o', linewidth=3)
    ax1.plot(times, to_arr("tot_service"),
             color='red', marker='o', label='Total Service')
    ax1.plot(times, to_arr("tot_arrival"),
             color='blue', marker='o', label='Total Arrival')
    ax1.plot(times, to_arr("tot_arrival") - to_arr("tot_lost"),
             color='lightblue', marker='o', label='Total Arrival Accepted')

    # Print incr/decr allowed
    if cfg.cca == "copa":
        print("Copa queueing delay calculation. Format [incr/decr/qdel]")
        for n in range(cfg.N):
            print(f"Flow {n}")
            for t in range(cfg.T):
                print("{:<3}".format(t), end=": ")
                for dt in range(cfg.T):
                    iname = f"incr_allowed_{n},{t},{dt}"
                    dname = f"decr_allowed_{n},{t},{dt}"
                    qname = f"qdel_{t},{dt}"
                    if iname not in m:
                        print(f" - /{int(m[qname])}", end=" ")
                    else:
                        print(
                            f"{int(m[iname])}/{int(m[dname])}/{int(m[qname])}",
                            end=" ")
                print("")

    col_names: List[str] = ["wasted", "tot_service", "tot_arrival", "tot_lost"]
    per_flow: List[str] = ["loss_detected", "last_loss", "cwnd", "rate"]
    if cfg.cca == "bbr":
        for n in range(cfg.N):
            print("BBR start state = ", m[f"bbr_start_state_{n}"])
        per_flow.extend(["max_rate"])

    cols: List[Tuple[str, Optional[int]]] = [(x, None) for x in col_names]
    for n in range(cfg.N):
        for x in per_flow:
            if x == "last_loss" and cfg.cca != "aimd":
                continue
            cols.append((x, n))
            col_names.append(f"{x}_{n}")

    # Print when we timed out
    for n in range(cfg.N):
        print(f"Flow {n} timed out at: ",
              [t for t in range(cfg.T) if m[f"timeout_{n},{t}"]])

    print("\n", "=" * 30, "\n")
    print(("t  " + "{:<15}" * len(col_names)).format(*col_names))
    for t, vals in enumerate(zip(*[list(to_arr(*c)) for c in cols])):
        v = ["%.10f" % v for v in vals]
        print(f"{t: <2}", ("{:<15}" * len(v)).format(*v))

    for n in range(cfg.N):
        args = {'marker': 'o', 'linestyle': linestyles[n]}

        if cfg.N > 1:
            ax1.plot(times, to_arr("service", n) - adj,
                     color='red', label='Egress %d' % n, **args)
            ax1.plot(times, to_arr("arrival", n) - adj,
                     color='blue', label='Ingress %d' % n, **args)

        ax1.plot(times, to_arr("losts", n) - adj,
                 color='orange', label='Num lost %d' % n, **args)
        ax1.plot(times, to_arr("loss_detected", n)-adj,
                 color='yellow', label='Num lost detected %d' % n, **args)

        ax2.plot(times, to_arr("cwnd", n),
                 color='black', label='Cwnd %d' % n, **args)
        ax2_rate.plot(times, to_arr("rate", n),
                      color='orange', label='Rate %d' % n, **args)

    # Determine queuing delay
    if not cfg.simplify and cfg.calculate_qdel:
        # This doesn't work with simplification, since numerical errors creep
        # up
        qdel_low = []
        qdel_high = []
        A = to_arr("tot_arrival", frac=True)
        L = to_arr("tot_lost", frac=True)
        S = to_arr("tot_service", frac=True)
        for t in range(cfg.T):
            dt_found = None
            if t > 0 and S[t] == S[t-1]:
                assert(dt_found is None)
                qdel_low.append(qdel_low[-1])
                qdel_high.append(qdel_high[-1])
                dt_found = qdel_low[-1]
                continue
            for dt in range(t):
                if A[t-dt] - L[t-dt] == S[t] \
                   and (t-dt == 0 or A[t-dt] - L[t-dt] != A[t-dt-1] - L[t-dt-1]):
                    assert(dt_found is None)
                    dt_found = dt
                    qdel_low.append(dt)
                    qdel_high.append(dt)
                if A[t-dt-1] - L[t-dt-1] < S[t] and A[t-dt] - L[t-dt] > S[t]:
                    assert(dt_found is None)
                    dt_found = dt
                    qdel_low.append(dt)
                    qdel_high.append(dt+1)
            if A[0] - L[0] > S[t]:
                # Only lower bound is known
                assert(dt_found is None)
                qdel_low.append(t)
                qdel_high.append(1e9)  # Infinity
                dt_found = t
            if A[0] - L[0] == S[t]:
                assert(dt_found is None)
                qdel_low.append(t)
                qdel_high.append(t)
                dt_found = t
            assert(dt_found is not None)
        max_qdel = max([x for x in qdel_high if x != 1e9])
        ax2_rtt.set_ylim(min(qdel_low), max_qdel)
        ax2_rtt.fill_between(times, qdel_high, qdel_low,
                             color="skyblue", alpha=0.5, label="Q Delay")

    ax1.legend()
    ax2.legend(loc="upper left")
    ax2_rate.legend(loc="upper center")
    ax2_rtt.legend(loc="upper right")
    plt.savefig('multi_flow_plot.svg')
    plt.show()

    generate_incal_trace(m, cfg)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 plot.py cache_file_name [simp]", file=sys.stderr)
        exit(1)
    try:
        f = open(sys.argv[1], 'rb')
        qres: QueryResult = pkl.load(f)
    except Exception as e:
        print("Exception while loacing cached file")
        print(e)

    print(qres.satisfiable)
    if qres.satisfiable == "sat":
        assert(qres.model is not None)
        plot_model(qres.model, qres.cfg)
    else:
        print("The query was unsatisfiable, so there is nothing to plot")
