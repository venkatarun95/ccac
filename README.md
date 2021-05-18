# Verification of Congestion Control Algorithms with a SMT Solver

## Files

* `model.py`: contains the main network model
* `cca\_aimd.py`: Implementation of AIMD
* `cca\_bbr.py`: Implementation of BBR
* `cca\_bbr\_rtt.py`: A more complete implementation of BBR where the cwnd updates once every RTT instead of RTT\_min. This does not currently work
* `aimd_proofs.py`: `prove_loss_bounds` proves AIMD's steady state. The other functions explore some other properties of AIMD empirically
* `cca_copa.py`: Not yet implemented
* `model_test.py`: a few property-based tests for model.py

Utility files:
* `model_utils.py`: contains a) the config struct, b) the variables struct which contains all Z3 global variables and c) a function to plot the results
* `plot.py`: Thin CLI wrapper around `plot_model` in `model_utils.py`
* `clean_output.py`: takes a Z3 result and uses local gradient descent to simplify it somewhat. Can usually be invoked using the `--simplify` flag or the `simplify` property in `ModelConfig`
* `cache.py`: runs and caches Z3 queries
* `my_solver.py`: a thin wrapper over the Python z3 wrapper
* `binary_search.py`: a utility. E.g. if we want to know the minimum utilization of Copa, we could use binary search. This also handles the result `unknown` in addition to `sat` and `unsat` that Z3 outputs.

## Running

First make a `cached` folder. To make queries, you can modify the `__main__` part of `model.py` and run it or run `aimd_proofs.py` with the given CLI arguments. Results can be plotted using `plot.py` by giving it the name of the cache file (if the result is unsat, obviously it won't plot anything).

## Dependencies

We use Z3 as the SMT solver. Install the Z3 package for Python with:
```bash
pip install z3-solver
```

We also need matplotlib
