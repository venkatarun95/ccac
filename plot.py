import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import pickle as pkl
import sys
from typing import List, Optional, Tuple, Union

from pyz3_utils import QueryResult
from config import ModelConfig
from utils import ModelDict
from variables import VariableNames


def plot_model(m: ModelDict, c: ModelConfig, v: VariableNames):
    def to_arr(names: Union[List[str], List[List[str]], str],
               n: Optional[int] = None, frac=False) -> np.ndarray:
        if type(names) == str:
            # Sometimes name is a str, for instance when it is an internal CCA
            # variable and not available in Variables. In this case, we
            # directly convert to list
            if n is None:
                names = [f"{names}_{t}" for t in range(c.T)]
            else:
                names = [f"{names}_{n},{t}" for t in range(c.T)]
        else:
            if n is not None:
                assert type(names[0]) == list
                names = names[n]
            else:
                assert type(names[0]) == str
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
    # if c.dupacks is None:
    #     print("dupacks = ", m[v.dupacks])
    if c.cca in ["aimd", "fixed_d", "copa"] and c.alpha is None:
        print("alpha = ", v.alpha)
    if not c.compose:
        print("epsilon = ", v.epsilon)

    # Configure the plotting
    fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
    fig.set_size_inches(18.5, 10.5)
    ax1.grid(True)
    ax2.grid(True)
    ax2.set_xticks(range(0, c.T))
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
    times = [t for t in range(c.T)]
    ct = np.asarray([c.C * t for t in range(c.T)])

    ax1.plot(times, ct - np.asarray(v.W),
             color='black', marker='o', label='Bound', linewidth=3)
    ax1.plot(times[c.D:], (ct - to_arr("wasted"))[:-c.D],
             color='black', marker='o', linewidth=3)
    ax1.plot(times, np.asarray(v.S),
             color='red', marker='o', label='Total Service')
    ax1.plot(times, np.asarray(v.A),
             color='blue', marker='o', label='Total Arrival')
    ax1.plot(times, np.asarray(v.A) - np.asarray(v.L),
             color='lightblue', marker='o', label='Total Arrival Accepted')

    # Print incr/decr allowed
    if c.cca == "copa":
        print("Copa queueing delay calculation. Format [incr/decr/qdel]")
        for n in range(c.N):
            print(f"Flow {n}")
            for t in range(c.T):
                print("{:<3}".format(t), end=": ")
                for dt in range(c.T):
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

    acc_flows: List[Any] = [v.W, v.S, v.A, v.L]
    acc_flows_names: List[str] = ["W", "S", "A", "L"]
    per_flow: List[Any] = [v.Ld_f, v.c_f, v.r_f]
    per_flow_names: List[str] = ["Ld_f", "c_f", "r_f"]
    if c.cca == "aimd":
        per_flow.append("last_loss")
    if c.cca == "bbr":
        for n in range(c.N):
            print("BBR start state = ", m[f"bbr_start_state_{n}"])
            per_flow.extend(["max_rate"])

    # def printable(names) -> str:
    #     '''Create a human friendly name from the list after stripping
    #     "{n},{t}"'''
    #     if type(names) == str:
    #         name = x
    #     else:
    #         assert type(names) == list
    #         if type(names[0]) == str:
    #             name = names[0]
    #         elif type(names[0]) == list:
    #             name = names[0][0]
    #         name = '_'.join(name.split('_')[:-1])
    #     return name

    cols = acc_flows
    col_names: List[str] = acc_flows_names
    for n in range(c.N):
        for (x, name) in zip(per_flow, per_flow_names):
            cols.append(x[n])
            col_names.append(f"{name}_{n}")

    # Print when we timed out
    for n in range(c.N):
        print(f"Flow {n} timed out at: ",
              [t for t in range(c.T) if m[f"timeout_{n},{t}"]])

    print("\n", "=" * 30, "\n")
    print(("t  " + "{:<15}" * len(col_names)).format(*col_names))
    for t, vals in enumerate(zip(*[c for c in cols])):
        vals = ["%.10f" % float(v) for v in vals]
        print(f"{t: <2}", ("{:<15}" * len(vals)).format(*vals))

    for n in range(c.N):
        args = {'marker': 'o', 'linestyle': linestyles[n]}

        if c.N > 1:
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
    if not c.simplify and c.calculate_qdel:
        # This doesn't work with simplification, since numerical errors creep
        # up
        qdel_low = []
        qdel_high = []
        A = v.A
        L = v.L
        S = v.S
        for t in range(c.T):
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
