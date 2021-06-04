# Formally Verifying Congestion Control Performance

This code-base accompanies the SIGCOMM 2021 paper "Formally Verifying Congestion Control Performance" by Venkat Arun, Mina Arashloo, Ahmed Saeed, Mohammad Alizadeh and Hari Balakrishnan

## Dependencies

We use Z3 as the SMT solver. Install the Z3 and its Python bindings from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3)

We also need matplotlib, numpy and scipy. This project needs Python 3.8.5+

## Running

First ensure there is a `cached` folder. To make queries, you can modify the `__main__` part of `model.py`. Results can be plotted using `plot.py` by giving it the name of the cache file; if the result is unsat it naturally won't plot anything, because there is no satisfying assignment to plot. The result of computation can be `unknown`. Since we have restricted ourselves to decidable logic, `unknown` only occurs if Z3 hasn't had enough time to compute. In our experience, if the number of timesteps <= 20, it never takes more than 10 minutes to compute.

The proofs about AIMD and Copa in the paper are in `aimd_proofs.py` and `copa_proofs.py`. To check the proofs just run the respective Python files. The files contain multiple lemmas which when stitched together prove that the CCA will eventually enter the steady state, and once entered remain there. If Z3 is able to prove a lemma, it will output `unsat`. If all lemmas are proved, the file will terminate successfully, which means the theorem in the paper is proven. Refer the paper and `variables.py` for what the variables mean. The lemmas should be clear from the code and comments. Each lemma has the form p —> q, where p are a set of assumptions and q is the property we want to prove. Note that to prove p —> q, we ask the solver to show that its negation, i.e., p /\ ~q, is unsatisfiable.

We have created three examples of behaviors that CCAC uncovers in `example_queries.py`, one for each of the three algorithms: AIMD, BBR and Copa. An example command is `python3 example_queries.py copa_low_util`. It will output both a graph and print a table of values picked by the solver.

## Understanding the output

When using `cache.py` to run Z3, the model (i.e. variable assignments computed by CCAC) are saved in the `cached/` folder. These can be plotted by calling `python3 plot.py <cache-file-name>`. Plots can also be created from code.

### The plot
In this section, we explain the plots and output. The x-axis is in timesteps, which is (1 / c.R) RTTs. Typically, c.R=1 so 1 timestep=1 RTT. It will plot two graphs. On the top, it will plot curves like A(t), S(t), the bounds on S(t) (the black lines = C * t-W(t)). These are all cumulative curves where the y axis is in amount of data (bytes, megabytes). Since units are arbitrary, we set the link rate C = 1. On the bottom it will plot the congestion window (cwnd), pacing rate and queuing delay. Please be mindful that all three have separate scales on the y-axis. Queuing delay can be a range, as explained in section 5 of the paper; the solver is free to assume the queuing delay can take any value within that range. Queuing delay is not plotted when the simplification procedure is used, since numerical errors affect range computation (see below).

### The printed output
In addition to the plot, CCAC prints interesting values from the solution. This includes additional information, for instance the `alpha` value it picked. `alpha` is the size of MSS, which the solver is usually allowed to pick. The solver's choice of `alpha` implicitly sets the link rate as `C` / `alpha` is the link rate in MSS/timestep. Similarly, it prints `dupacks` and internal variables of various CCAs. You can look at the code for the individual CCAs and `plot.py` for details. The plotting function may print a value of -1 if the value was unassigned by the solver. Note, Z3 internally represents numbers as fractions, which is why `plot.py` will print some numbers in fraction form for some variables to avoid losing information.

### Simplification
If you choose to use `clean_output.py` to simplify the solution, keep in mind that the procedure uses finite precision floating point numbers. This is in contrast to Z3 with uses arbitrary precision rational arithmetic. Hence you may see some numerical errors which can make the solution inconsistent with the constraints. E.g. you may see small negative values for loss, while the constraint loss >= 0 is there in the constraints.

The simplification procedure just tries to make the lines a little straighter. It does not always accomplish much. As a rule of thumb, the more extreme the query, the more understandable the output will be. For instance, Copa under the network model where the path-server doesn't compose, Copa achieves >=50% utilization with the query in `example_queries.py`. The output for thresholds near 50% are cleaner than for higher thresholds, since Z3 has less 'play' to make arbitrary decisions.


## Files

The following files contain SMT constraints that express the logic in the paper

* `model.py`: contains the main network model
* `cca_aimd.py`: Implementation of AIMD
* `cca_bbr.py`: Implementation of BBR
* `cca_copa.py`: Implementation of Copa
* `aimd_proofs.py`: `prove_loss_bounds` proves AIMD's steady state
* `copa_proofs.py`: `prove_loss_bounds` proves Copa's steady state
* `test_model.py`: Property-based unit tests for `model.py`
* `test_cca_aimd.py`: Property-based unit tests for `cca_aimd.py`

Utility files

* `config.py`
* `variables.py` Has the `Variables` struct which has all Z3 global variable
* `utils.py`: Definition of `ModelDict`, which contains Z3's output assignment to variables
* `plot.py`: Plots model. Can be used as a library and standalone from a cache file. See "understanding the output" for details
* `clean_output.py`: takes a Z3 result and uses local gradient descent to simplify it somewhat. Can usually be invoked using the `--simplify` flag or the `simplify` property in `ModelConfig`. Note, since this uses fixed-precision numbers, its output can be inconsistent with the constraint. For instance, you may see a small negative number for loss. Z3's non-simplified output (which is often simple enough) by contrast is always consistent since it uses arbitrary precision rational arithmetic
* `cache.py`: runs and caches Z3 queries
* `my_solver.py`: a thin wrapper over the Python z3 wrapper
* `binary_search.py`: a utility. E.g. if we want to know the minimum utilization of Copa, we could use binary search. This also handles the result `unknown` in addition to `sat` and `unsat` that Z3 outputs.
