import sys
from typing import List
from z3 import And, ArithRef, If, Implies, Not, Or

from config import ModelConfig
import variables
from my_solver import MySolver


class App:
    # Cumulative number of bytes that the app can send at this point
    snd: List[ArithRef]

    def implement(self, c: ModelConfig, s: MySolver, v: variables.Variables):
        print("App needs to override the 'implement' function",
              file=sys.stderr)
        exit(1)


class BufferBasedConfig:
    def __init__(self, n):
        # The CCA flow id we are using
        self.n = n
        # Number of distinct chunk sizes
        self.N_c = 4
        # margin of error on chunk sizes
        self.chunk_margin = 0.1


class BufferBasedVariables:
    def __init__(self, ac: BufferBasedConfig, c: ModelConfig, s: MySolver):
        # Assume all chunks encode the same amount of time (in timesteps)
        self.chunk_time = s.Real(f"chunk_time_{ac.n}")

        # The chunk sizes in units of data
        self.Ch_s = [s.Real(f"chunk_size_{ac.n},{i}") for i in range(ac.N_c)]
        # The playback buffer length (in timesteps) above which we we will use
        # the i^th chunk. The smallest threshold is always 0
        self.Ch_t = [0] + \
            [s.Real(f"chunk_thresh_{ac.n},{i+1}") for i in range(ac.N_c-1)]

        # Playback buffer length at time t
        self.b = [s.Real(f"buffer_{ac.n},{t}") for t in range(c.T)]
        # Cumulative number of bytes (from the beginning) to be downloaded for
        # the next chunk to finish downloading. Also the number of packets sent
        # by the sender (i.e. app limit amount)
        self.snd = [s.Real(f"app_snd_{ac.n},{t}") for t in range(c.T)]
        # Chunk size chosen by the algorithm at time t. Only well defined when
        # Ch_fin is true
        self.Ch_s_chosen = [s.Real(f"chunk_size_chosen_{ac.n},{t}")
                            for t in range(c.T)]
        # Whether or not a chunk just finished
        self.Ch_fin = [s.Bool(f"chunk_finished_{ac.n},{t}")
                       for t in range(c.T)]


def initial(ac: BufferBasedConfig, av: BufferBasedVariables, c: ModelConfig,
            s: MySolver, v: variables.Variables):
    s.add(av.chunk_time >= 1)
    s.add(av.Ch_s[0] > 0)
    s.add(av.Ch_t[1] > 0)
    s.add(Or(*[av.snd[0] == av.Ch_s[i] for i in range(ac.N_c)]))
    s.add(av.b[0] >= 0)


def monotone(ac: BufferBasedConfig, av: BufferBasedVariables, c: ModelConfig,
             s: MySolver, v: variables.Variables):
    for i in range(1, ac.N_c):
        s.add(av.Ch_s[i - 1] <= av.Ch_s[i])
        s.add(av.Ch_t[i - 1] <= av.Ch_t[i])

    for t in range(1, c.T):
        s.add(av.b[t - 1] <= av.b[t])
        s.add(av.snd[t - 1] <= av.snd[t])


def track_buffer(ac: BufferBasedConfig, av: BufferBasedVariables,
                 c: ModelConfig, s: MySolver, v: variables.Variables):
    ''' Track the variables b, dwnl and played '''
    for t in range(1, c.T):
        # Did the chunk currently being downloaded finish?
        s.add(av.Ch_fin[t] == (av.snd[t-1] <= v.S_f[ac.n][t] - v.S_f[ac.n][0]))
        # Set the length of the playback buffer
        s.add(Implies(av.Ch_fin[t], av.b[t] == av.b[t-1] - 1 + av.chunk_time))
        s.add(Implies(Not(av.Ch_fin[t]),
                      av.b[t] == If(av.b[t-1] < 1, 0, av.b[t-1] - 1)))

        # Select the chunk size to download next based on the current buffer
        # size
        chunk_size = s.Real(f"chunk_size_chosen_{ac.n},{t}")
        for i in range(1, ac.N_c):
            s.add(Implies(And(av.Ch_t[i-1] <= av.b[t], av.b[t] < av.Ch_t[i]),
                          av.Ch_s_chosen[t] == av.Ch_s[i-1]))
        s.add(Implies(av.Ch_t[ac.N_c-1] <= av.b[t],
                      av.Ch_s_chosen[t] == av.Ch_s[ac.N_c-1]))

        # Add to dwnl with some margin of error
        s.add(Implies(av.Ch_fin[t], av.snd[t]
                      <= av.snd[t-1] + chunk_size * (1 + ac.chunk_margin)))
        s.add(Implies(av.Ch_fin[t], av.snd[t]
                      >= av.snd[t-1] + chunk_size * (1 - ac.chunk_margin)))
        s.add(Implies(Not(av.Ch_fin[t]), av.snd[t] == av.snd[t-1]))


def make_abr_periodic(ac: BufferBasedConfig, av: BufferBasedVariables,
                      _c: ModelConfig, s: MySolver, v: variables.Variables):
    s.add(av.b[0] == av.b[-1])
    s.add(av.snd[0] - v.S_f[ac.n][0] == av.snd[-1] - v.S_f[ac.n][-1])


def make_buffer_based_app(n: int, c: ModelConfig, s: MySolver,
                          v: variables.Variables):
    ac = BufferBasedConfig(n)
    av = BufferBasedVariables(ac, c, s)
    initial(ac, av, c, s, v)
    monotone(ac, av, c, s, v)
    track_buffer(ac, av, c, s, v)
    return (ac, av)
