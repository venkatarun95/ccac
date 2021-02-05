from multi_flow import ModelConfig
from cache import QueryResult
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
from typing import Dict, List, Optional, Tuple, Union
import pickle as pkl

def plot_model(m: Dict[str, Union[float, bool]], cfg: ModelConfig):
    # matplotlib.rc('xtick', labelsize=20)
    # matplotlib.rc('ytick', labelsize=20)
    matplotlib.rc("font", size=40)

    def to_arr(name: str, n: Optional[int] = None) -> np.array:
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
        return np.array(res)

    # Configure the plotting
    fig, ax1 = plt.subplots(1, 1, sharex=True)
    fig.set_size_inches(18.5, 10.5)
    ax1.grid(True)

    times = [t for t in range(cfg.T)]
    ct = np.asarray([cfg.C * t for t in range(cfg.T)])

    wasted = to_arr("wasted")
    out = to_arr("tot_out")
    inp = to_arr("tot_inp")

    between = [(0, inp[0])]
    for t in range(1, len(out)):
        between.append((t, out[t]))
        between.append((t, inp[t]))
    between.append((len(out) - 1, out[-1]))
    between_times, between_bytes = zip(*between)
    ax1.plot(between_times, between_bytes, color="orange", linestyle="--", label='S₁(t) = A₂(t)')


    wasted[-1] = wasted[-2] + 0.9
    ax1.plot(times, ct - wasted,
             color='black', marker='o', label='Bounds', linewidth=3)
    ax1.plot(times[cfg.D:], (ct - wasted)[:-cfg.D],
             color='black', marker='o', linewidth=3)
    ax1.plot(times, out,
             color='red', marker='o', label='S(t)')
    ax1.plot(times, inp,
             color='blue', marker='o', label='A(t)')
    # ax1.plot(times, to_arr("tot_inp") - to_arr("tot_lost"),
    #          color='lightblue', marker='o', label='Total Ingress Accepted')


    ax1.set_xlabel("Time (Rₘ)")
    ax1.set_ylabel("Cumulative bytes (in BDP)")
    x_left, x_right = ax1.get_xlim()
    y_low, y_high = ax1.get_ylim()
    ax1.set_aspect(abs((x_right-x_left)/(y_low-y_high))/2)
    ax1.legend()
    plt.savefig('/home/venkatar/Downloads/copa-z3.pdf')
    plt.show()

if __name__ == "__main__":
    f = open("cached/d2c00c416b9fd84c.cached", "rb")
    qres: QueryResult = pkl.load(f)
    plot_model(qres.model, qres.cfg)
