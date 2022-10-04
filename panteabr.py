from abr import App
from config import ModelConfig
from my_solver import MySolver
from variables import Variables
from z3 import If

class PanteABRVariables:
    def __init__(self, n: int, c: ModelConfig, s: MySolver, v: Variables):
        # Cap on the cumulative number of bytes to be sent
        self.snd = [s.Real(f"app_snd_{n},{t}") for t in range(c.T)]
        # Amount of real data made available this timestep
        self.encoded = [s.Real(f"app_encoded_{n},{t}") for t in range(c.T)]
        # Total cap on amount of real data that can be sent
        self.encoded_tot = [s.Real(f"app_encoded_tot_{n},{t}") for t in range(c.T)]
        # Dummy data we have sent so far (cumulative)
        self.actually_sent = [s.Real(f"app_actually_sent_{n},{t}") for t in range(c.T)]

def make_panteabr_app(n: int, c: ModelConfig, s: MySolver, v: Variables):
    av = PanteABRVariables(n, c, s, v)

    for t in range(c.T):
        if t == 0:
            rate = v.c_f[n][t] / c.R
        else:
            rate = (v.A_f[n][t] - v.A_f[n][t-1]) / c.R
        s.add(av.encoded[t] <= rate)
        s.add(av.encoded[t] >= rate * 0.8)

        if t > 0:
            s.add(av.snd[t] == 1000)
            s.add(av.encoded_tot[t] == av.encoded_tot[t-1] + av.encoded[t])
            could_send = v.A_f[n][t] - v.A_f[n][t-1]
            available_to_send = av.encoded_tot[t] - av.actually_sent[t-1]
            s.add(av.actually_sent[t] == av.actually_sent[t-1] +
                  If(could_send < available_to_send, could_send, available_to_send))

    return (None, av)
