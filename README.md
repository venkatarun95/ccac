# Verification of Congestion Control Algorithms with a SMT Solver

## Dependencies

We use Z3 as the SMT solver. Install the Z3 package for Python with:
```bash
pip install z3-solver
```

We also need matplotlib and scipy. This project needs Python 3.5+ since it uses type annotations.

## Running

First make a `cached` folder. To make queries, you can modify the `__main__` part of `model.py`. Results can be plotted using `plot.py` by giving it the name of the cache file; if the result is unsat, obviously it won't plot anything, because there is no satisfying assignment to plot. The result of computation can be `unsat`. Since we have restricted ourselves to decidable logic, `unsat` only occurs if Z3 hasn't had enough time to compute. In our experience, if the number of timesteps <= 20, it never takes more than 10 minutes to compute.

The proofs about AIMD and Copa in the paper are in `aimd_proofs.py` and `copa_proofs.py`. To check the proofs just run the respective Python files. The files contain multiple lemmas which when stitched together prove that the CCA will eventually enter the steady state, and once entered remain there. If Z3 is able to prove a lemma, it will output `unsat`, and terminate successfully. The lemmas should be clear from the code and comments. Refer the paper for what the variables mean.

## Files

The following file contains SMT constraints that express the logic in the paper

* `model.py`: contains the main network model
* `cca_aimd.py`: Implementation of AIMD
* `cca_bbr.py`: Implementation of BBR
* `cca_bbr_rtt.py`: A more complete implementation of BBR where the cwnd updates once every RTT instead of RTT\_min. This does not currently work
* `aimd_proofs.py`: `prove_loss_bounds` proves AIMD's steady state
* `copa_proofs.py`: `prove_loss_bounds` proves Copa's steady state
* `cca_copa.py`: Not yet implemented
* `test_model.py`: Property-based tests for `model.py`
* `test_cca_aimd.py`: Property-based tests for `cca_aimd.py`

Utility files

* `config.py`
* `variables.py` Has the `Variables` struct which has all Z3 global variable
* `utils.py`: Definition of `ModelDict`, which contains Z3's output assignment to variables
* `plot.py`: Plots model. Can be used as a library and standalone from a cache file
* `clean_output.py`: takes a Z3 result and uses local gradient descent to simplify it somewhat. Can usually be invoked using the `--simplify` flag or the `simplify` property in `ModelConfig`
* `cache.py`: runs and caches Z3 queries
* `my_solver.py`: a thin wrapper over the Python z3 wrapper
* `binary_search.py`: a utility. E.g. if we want to know the minimum utilization of Copa, we could use binary search. This also handles the result `unknown` in addition to `sat` and `unsat` that Z3 outputs.
