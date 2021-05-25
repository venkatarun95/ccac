'''
Runs the SMT query while caching the result of every query ever run. Assumes
that the mapping from the Solver::to_smt2 string to sat/unsat/unknown
is deterministic if query returned without timeout. If answer is unknown
because of timeout, makes note of that
'''

import hashlib
import multiprocessing as mp
import os
import pickle as pkl
from typing import Dict, Optional, Union
from my_solver import MySolver
from z3 import Solver, parse_smt2_string

import clean_output
from config import ModelConfig
from utils import model_to_dict


class QueryResult:
    satisfiable: str
    model: Optional[Dict[str, Union[float, bool]]]
    timeout: Optional[float]
    cfg: Optional[ModelConfig]

    def __init__(
        self,
        satisfiable: str,
        model: Optional[Dict[str, Union[float, bool]]],
        timeout: Optional[float],
        cfg: ModelConfig,
    ):
        ''' Arguments:
        satisfiable - one of 'sat', 'unsat', 'unknown'
        model - a map of variable assignments in the model
        timeout - If execution timed out, the timeout value in seconds
        '''
        if timeout is not None:
            assert(satisfiable == "unknown")

        self.satisfiable = satisfiable
        self.model = model
        self.timeout = timeout
        self.cfg = cfg


# Nope, let us run the query
def run(queue, assertion_list, track_unsat, cfg):
    s = Solver()
    s.set(unsat_core=track_unsat)
    for (i, e) in enumerate(assertion_list):
        e = parse_smt2_string(e)[0]
        s.assert_and_track(e, f"{str(e)} :{i}")
    satisfiable = s.check()
    if cfg.unsat_core and str(satisfiable) == "unsat":
        print(s.unsat_core())
    queue.put(str(satisfiable))
    if str(satisfiable) == "sat":
        model = model_to_dict(s.model())
        queue.put(model)
    else:
        queue.put(None)


def run_query(
    s: MySolver,
    cfg: ModelConfig,
    timeout: float = 10,
    dir: str = "cached"
) -> QueryResult:
    '''
    `timeout` is the maximum execution time.
    `dir` is the directory in which all the cache files are stored (and will
        be stored by this function)
    '''

    # We also add cfg.simplify to the hash because simplification changes the
    # SMT output, and we don't want the caching mechanism to rely on the
    # correctness of anything other than the SMT solver
    s_hash = hashlib.sha256(
        (s.to_smt2() + str(cfg.simplify)).encode("utf-8")
    ).digest().hex()[:16]
    fname = dir + "/" + s_hash + ".cached"
    print(f"Cache file name: {fname}")
    if not cfg.unsat_core and os.path.exists(fname):
        # Read cached
        try:
            f = open(fname, 'rb')
            res: QueryResult = pkl.load(f)
            if res.timeout is None:
                # We got the result last time. Just return it
                print("Cache hit")
                return res
            elif res.timeout >= timeout:
                # Was the timeout last time >= timeout now? If so, we'll just
                # timeout again. So return what we had last time
                print("Cache hit")
                return res
        except Exception as e:
            print("Warning: exception while opening cached file %s" % fname)
            print(e)

    queue = mp.Manager().Queue()

    def to_smt2(e):
        s = Solver()
        s.add(e)
        return s.to_smt2()
    assertion_list = [to_smt2(e) for e in s.assertion_list]
    proc = mp.Process(target=run,
                      args=(queue, assertion_list, s.track_unsat, cfg))
    proc.start()
    proc.join(timeout)
    timed_out: bool = False
    if proc.is_alive():
        timed_out = True
        proc.terminate()
        proc.join()

    if not timed_out:
        satisfiable = queue.get()
        model = queue.get()
        if satisfiable == "sat" and cfg.simplify:
            print("Simplifying")
            model = clean_output.simplify_solution(cfg, model, s.assertions())

        res = QueryResult(satisfiable, model, None, cfg)
    else:
        res = QueryResult("unknown", None, timeout, cfg)

    proc.close()

    # Cache it for next time
    try:
        f = open(fname, 'wb')
        pkl.dump(res, f)
        f.close()
    except Exception as e:
        print("Warning: exception while saving to cached file %s" % fname)
        print(e)

    return res
