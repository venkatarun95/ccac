import pickle as pkl
import sys

from cache import QueryResult
from model_utils import plot_model

if __name__ == "__main__":
    try:
        f = open(sys.argv[1], 'rb')
        qres: QueryResult = pkl.load(f)
    except Exception as e:
        print("Exception while loacing cached file")
        print(e)
    print(qres.satisfiable)
    if qres.satisfiable == "sat":
        print(qres)
        assert(qres.model is not None)
        plot_model(qres.model, qres.cfg)
