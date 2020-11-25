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
from z3 import Solver

from multi_flow import model_to_dict


class QueryResult:
    def __init__(
        self,
        satisfiable: str,
        model: Optional[Dict[str, Union[float, bool]]],
        timeout: Optional[float]
    ):
        ''' Arguments:
        satisfiable - one of 'sat', 'unsat', 'unknown'
        model - a map of variable assignments in the model
        timeout - If execution timed out, the timeout value in seconds
        '''
        if timeout is not None:
            assert(satisfiable == "unknown")

        self.model = model
        self.timeout = timeout
        self.satisfiable = satisfiable


def run_query(
    s: Solver,
    timeout: float = 10,
    dir: str = "cached"
) -> QueryResult:
    '''
    `timeout` is the maximum execution time.
    `dir` is the directory in which all the cache files are stored (and will
        be stored by this function)
    '''

    s_hash = hashlib.sha256(s.to_smt2().encode("utf-8")).digest().hex()[:16]
    fname = dir + "/" + s_hash + ".cached"
    if os.path.exists(fname):
        # Read cached
        try:
            f = open(fname, 'rb')
            res: QueryResult = pkl.load(f)
            if res.timeout is None:
                # We got the result last time. Just return it
                return res
            elif res.timeout >= timeout:
                # Was the timeout last time >= timeout now? If so, we'll just
                # timeout again. So return what we had last time
                return res
        except Exception as e:
            print("Warning: exception while opening cached file %s" % fname)
            print(e)

    # Nope, let us run the query
    def run(queue):
        satisfiable = s.check()
        queue.put(str(satisfiable))
        if str(satisfiable) == 'sat':
            model = model_to_dict(s.model())
            queue.put(model)
        else:
            queue.put(None)

    queue = mp.Manager().Queue()
    proc = mp.Process(target=run, args=(queue,))
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
        res = QueryResult(satisfiable, model, None)
    else:
        res = QueryResult("unknown", None, timeout)

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
