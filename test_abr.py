import unittest
from z3 import And, Implies, Or

import abr
#from model import Variables, cwnd_rate_arrival, initial, monotone, network,\
#    relate_tot
import model
from config import ModelConfig
from my_solver import MySolver


class TestAbr(unittest.TestCase):
    def test_app_limited(self):
        # If there is stuff to send, we must send it
        for N in [1, 2]:
            c = ModelConfig.default()
            s = MySolver()
            c.N = N
            c.app = "bb_abr"
            v = model.Variables(c, s)
            c.ac = [abr.BufferBasedConfig(n) for n in range(N)]
            v.av = [abr.BufferBasedVariables(c.ac[n], c, s) for n in range(N)]

            model.cwnd_rate_arrival(c, s, v)
            model.initial(c, s, v)
            model.monotone(c, s, v)

            for n in range(N):
                abr.initial(c.ac[n], v.av[n], c, s, v)
                abr.monotone(c.ac[n], v.av[n], c, s, v)

                s.add(v.c_f[n][c.T // 2] > 0)
                s.add(v.r_f[n][c.T // 2] > 0)
                s.add(v.av[n].snd[c.T // 2] > 0)
                # This is implied when all constraints are present. Here it is
                # not
                s.add(v.A_f[n][0] >= 0)
                s.add(v.A_f[n][c.T - 1] == 0)

            sat = s.check()
            # from utils import model_to_dict
            # m = model_to_dict(s.model())
            # print(N)
            # for t in range(1, c.T):
            #     print("{:<5} {:<5} {:<5} {:<5}".format(
            #         float(m[f"arrival_0,{t}"]),
            #         float(m[f"app_snd_0,{t}"]),
            #         float(m[f"rate_0,{t}"]),
            #         float(m[f"cwnd_0,{t}"])
            #     ))
            self.assertEqual(str(sat), "unsat")


if __name__ == '__main__':
    unittest.main()
