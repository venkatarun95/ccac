from z3 import And

from cache import run_query
from model import make_solver, min_send_quantum
from config import ModelConfig


def prove_steady_state(timeout=10):
    c = ModelConfig.default()
    c.R = 2
    c.D = 1
    c.cca = "rocc"
    c.compose = True
    c.calculate_qdel = True
    c.unsat_core = False
    c.N = 1

    # The bigger this value is, the longer our T needs to be for some proofs
    # and the bigger max_queue
    max_min_rtt = 5
    max_queue = c.C * (max_min_rtt + 2*c.R + 2*c.D) + 1
    queue_ubound = c.C * (c.D + c.R)

    # At times before this, we do not have an estimate of cwnd if min RTT is as
    # large as max_min_rtt
    x = max_min_rtt + 2*c.R + 2*c.D + 1 + 1

    # Queue length decreases if it is higher than max_queue
    c.T = x + 2 * c.D + 1 + 1
    assert(x < c.T)
    s, v = make_solver(c)
    s.add(v.alpha < 1)
    s.add(v.cv.minrtt_f[0][0] <= max_min_rtt)
    # s.add(v.cv.probe[0] >= x)
    # s.add(v.cv.probe[0] + max_min_rtt + c.D < c.T)
    # assert(x + max_min_rtt + c.D < c.T)
    s.add(And(v.A_f[0][x] - v.L_f[0][x] - v.S_f[0][x] > max_queue,
              v.A_f[0][-1] - v.L_f[0][-1] - v.S_f[0][-1] >
              v.A_f[0][x] - v.L_f[0][x] - v.S_f[0][x] - c.C * c.D,
              v.A_f[0][-1] - v.L_f[0][-1] - v.S_f[0][-1] > max_queue))
    print("Proving that queue length decreases if greater than max_queue")
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # Number of undetected losses decreases
    # + 3 for 3 dupacks
    c.T = int(max_queue / c.C + 0.5) + 2 * (c.R + c.D) + 3
    s, v = make_solver(c)
    s.add(v.dupacks < 1)
     # Each timestamp, send at least as many bytes as dupacks
    s.add(v.dupacks == 3 * v.alpha)
    min_send_quantum(c, s, v)
    s.add(v.A_f[0][0] - v.L_f[0][0] - v.S_f[0][0] <= max_queue)
    s.add(And(v.L_f[0][0] - v.Ld_f[0][0] > 0,
              v.L_f[0][-1] - v.Ld_f[0][-1] > 0,
              v.L_f[0][-1] - v.Ld_f[0][-1] >
              v.L_f[0][0] - v.Ld_f[0][0] - c.C))
    print("Proving that number of undetected losses decreases")
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")

    # If utilization is low, cwnd increases
    c.T = x + 6 * (c.R + c.D)
    s, v = make_solver(c)
    s.add(v.L[0] == 0)
    s.add(v.cv.probe[0] == -1)
    s.add(v.alpha < 1)
    s.add(v.cv.minrtt_f[0][0] <= max_min_rtt)
    s.add(And(v.S[-1] - v.S[x] < c.C * (c.T - 1 - c.D - x), #0.825
              v.c_f[0][-1] <= 2 * v.c_f[0][x],
              v.c_f[0][-1] <= c.C * c.R))
    s.add(v.cv.probe[0] == -1)
    print("Proving that if utilization is low, cwnd increases")
    qres = run_query(s, c, timeout=1800)
    print(qres.satisfiable)
    # from plot import plot_model
    # plot_model(qres.model, c)
    assert(qres.satisfiable == "unsat")

    # If queue length is high, it decreases
    c.T = x + 6
    s, v = make_solver(c)
    s.add(v.L[0] == 0)
    s.add(v.alpha < 1)
    s.add(v.cv.minrtt_f[0][0] <= max_min_rtt)
    s.add(And(v.A[x] - v.L[x] - v.S[x] >
              c.C * (2 * c.R + 2 * c.D + v.cv.minrtt_f[0][x] + 1) + v.alpha,
              v.A[-1] - v.L[-1] - v.S[-1] >= v.A[x] - v.L[x] - v.S[x]))
    print("Proving that if queue length is high, it will decrease")
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    # from plot import plot_model
    # plot_model(qres.model, c)
    assert(qres.satisfiable == "unsat")

    # When queue length is less than C * min RTT when a probe happens, min RTT
    # estimate decreases
    c.T = x + max_min_rtt + 1 + c.D + 6*c.D
    s, v = make_solver(c)
    s.add(v.alpha < 1)
    s.add(v.cv.probe[0] >= 0)
    s.add(v.cv.probe[0] == x)
    s.add(v.A_f[0][x] - v.L_f[0][x] - v.S_f[0][x]
          <= c.C * (2 * c.R + 2 * c.D + v.cv.minrtt_f[0][x] + 1) + v.alpha)
    s.add(v.L_f[0][0] - v.Ld_f[0][0] == 0)
    s.add(And(v.cv.minrtt_f[0][x] > c.D,
              v.cv.minrtt_f[0][x] < max_min_rtt,
              v.cv.minrtt_f[0][-1] >= v.cv.minrtt_f[0][0]))
    print("Proving that min rtt will decrease if the queue is small enough")
    qres = run_query(s, c, timeout=600)
    print(qres.satisfiable)
    # from plot import plot_model
    # plot_model(qres.model, c)
    assert(qres.satisfiable == "unsat")

    # c.T = x + max_min_rtt + 1 + c.D + 2
    # s, v = make_solver(c)
    # s.add(v.alpha < 1)
    # s.add(v.L_f[0][0] - v.Ld_f[0][0] == 0)
    # s.add(v.cv.minrtt_f[0][0] < max_min_rtt)
    # # s.add(v.cv.probe[0] == -1)
    # qx = v.A_f[0][x] - v.L_f[0][x] - v.S_f[0][x]
    # qT = v.A_f[0][-1] - v.L_f[0][-1] - v.S_f[0][-1]
    # # s.add(qx < max_queue)
    # s.add(qx > c.C * (v.cv.minrtt_f[0][x] + c.R + 2*c.D + 1 + c.D) + v.alpha)
    # s.add(qT >= qx)
    # s.add(qT >= queue_ubound)
    # # If min RTT decreases, that's fine too
    # # s.add(v.cv.minrtt_f[0][x] == v.cv.minrtt_f[0][-1])
    # print("Proving that queue will decrease if the min_rtt is small enough")
    # print(f"x = {x}, max_min_rtt = {max_min_rtt}, T = {c.T}")
    # qres = run_query(s, c, timeout)
    # print(qres.satisfiable)
    # assert(qres.satisfiable == "unsat")

    return

    # When minRTT > 1, queue length always falls below some threshold
    c.T = x + max_min_rtt + 1
    s, v = make_solver(c)
    s.add(v.alpha < 1)
    s.add(v.L_f[0][0] - v.Ld_f[0][0] == 0)
    s.add(v.A_f[0][0] - v.L_f[0][0] - v.S_f[0][0] <= max_queue)
    s.add(v.A_f[0][-1] - v.L_f[0][-1] - v.S_f[0][-1]
          > c.C * (v.cv.minrtt_f[0][0] + c.D))
    s.add(v.A_f[0][-1] - v.L_f[0][-1] - v.S_f[0][-1] > queue_ubound)
    s.add(v.cv.minrtt_f[0][0] > min(1, c.D))
    print("Proving that queue will decrease if min rtt is small enough")
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    from plot import plot_model
    plot_model(qres.model, c)
    assert(qres.satisfiable == "unsat")


if __name__ == "__main__":
    prove_steady_state()
