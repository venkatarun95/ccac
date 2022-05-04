from typing import Any, List, Optional, Tuple

from config import ModelConfig
from pyz3_utils import MySolver
import pyz3_utils


class Variables(pyz3_utils.Variables):
    ''' Some variables that everybody uses '''

    def __init__(self, c: ModelConfig, s: MySolver,
                 name: Optional[str] = None):
        T = c.T

        # Add a prefix to all names so we can have multiple Variables instances
        # in one solver
        if name is None:
            pre = ""
        else:
            pre = name + "__"
        self.pre = pre

        # Naming convention: X_f denotes per-flow values (note, we only study
        # the single-flow case in the paper)

        # Cumulative number of bytes sent by flow n till time t
        self.A_f = [[s.Real(f"{pre}arrival_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        # Sum of A_f across all flows
        self.A = [s.Real(f"{pre}tot_arrival_{t}") for t in range(T)]
        # Congestion window for flow n at time t
        self.c_f = [[s.Real(f"{pre}cwnd_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        # Pacing rate for flow n at time t
        self.r_f = [[s.Real(f"{pre}rate_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        # Cumulative number of losses detected (by duplicate acknowledgements
        # or timeout) by flow n till time t
        self.Ld_f = [[s.Real(f"{pre}loss_detected_{n},{t}")
                      for t in range(T)]
                     for n in range(c.N)]
        # Cumulative number of bytes served from the server for flow n till
        # time t. These acks corresponding to these bytes will reach the sender
        # at time t+c.R
        self.S_f = [[s.Real(f"{pre}service_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        # Sum of S_f across all flows
        self.S = [s.Real(f"{pre}tot_service_{t}") for t in range(T)]
        # Cumulative number of bytes lost for flow n till time t
        self.L_f = [[s.Real(f"{pre}losts_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        # Sum of L_f for all flows
        self.L = [s.Real(f"{pre}tot_lost_{t}") for t in range(T)]
        # Cumulative number of bytes wasted by the server till time t
        self.W = [s.Real(f"{pre}wasted_{t}") for t in range(T)]
        # Whether or not flow n is timing out at time t
        self.timeout_f = [[s.Bool(f"{pre}timeout_{n},{t}") for t in range(T)]
                          for n in range(c.N)]

        # If qdel[t][dt] is true, it means that the bytes exiting at t were
        # input at time t - dt. If out[t] == out[t-1], then qdel[t][dt] ==
        # qdel[t-1][dt], since qdel isn't really defined (since no packets were
        # output), so we default to saying we experience the RTT of the last
        # received packet.

        # This is only computed when calculate_qdel=True since not all CCAs
        # require it. Of the CCAs implemented so far, only Copa requires it
        if c.calculate_qdel:
            self.qdel = [[s.Bool(f"{pre}qdel_{t},{dt}") for dt in range(T)]
                         for t in range(T)]

        # This is for the non-composing model where waste is allowed only when
        # A - L and S come within epsilon of each other. See in 'config' for
        # how epsilon can be configured
        if not c.compose:
            self.epsilon = s.Real(f"{pre}epsilon")

        # The number of dupacks that need to arrive before we declare that a
        # loss has occured by dupacks. Z3 can usually pick any amount. You can
        # also set dupacks = 3 * alpha to emulate the usual behavior
        if c.dupacks is None:
            self.dupacks = s.Real(f"{pre}dupacks")
            s.add(self.dupacks >= 0)
        else:
            self.dupacks = c.dupacks

        # The MSS. Since C=1 (arbitrary units), C / alpha sets the link rate in
        # MSS/timestep. Typically we allow Z3 to pick any value it wants to
        # search through the set of all possible link rates
        if c.alpha is None:
            self.alpha = s.Real(f"{pre}alpha")
            s.add(self.alpha > 0)
        else:
            self.alpha = c.alpha


class VariableNames:
    ''' Class with the same structure as Variables, but with just the names '''
    def __init__(self, v: Variables):
        for x in v.__dict__:
            if type(v.__dict__[x]) == list:
                self.__dict__[x] = self.to_names(v.__dict__[x])
            else:
                self.__dict__[x] = str(v.__dict__[x])

    @classmethod
    def to_names(cls, x: List[Any]):
        res = []
        for y in x:
            if type(y) == list:
                res.append(cls.to_names(y))
            else:
                if type(y) in [bool, int, float, tuple]:
                    res.append(y)
                else:
                    res.append(str(y))
        return res
