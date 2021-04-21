import pickle as pkl
import sys

from cache import QueryResult
from model_utils import plot_model

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 plot.py cache_file_name [simp]", file=sys.stderr)
        exit(1)
    try:
        f = open(sys.argv[1], 'rb')
        qres: QueryResult = pkl.load(f)
    except Exception as e:
        print("Exception while loacing cached file")
        print(e)

    print(qres.satisfiable)
    if qres.satisfiable == "sat":
        assert(qres.model is not None)
        plot_model(qres.model, qres.cfg)
