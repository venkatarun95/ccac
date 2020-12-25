from typing import List, Optional, Tuple


def sat_to_val(sat, reverse: bool = False):
    if sat == "sat":
        val = 3
    elif sat == "unknown":
        val = 2
    elif sat == "unsat":
        val = 1
    else:
        print(sat)
        assert(False)
    if reverse:
        val = 4 - val
    return val


class BinarySearch:
    '''  Binary search where there are three possibilities: 1, 2 and 3. We
    assume values are first 1s then 2s then 3s. Our job is to find the two
    boundaries. This is useful for when the SMT solver cannot find the answer

    At the end, results will be in is_1, is_2 and is_3
    '''

    is_1: float
    is_2: Optional[List[float]]
    is_3: float
    err: float
    found_1: bool
    # Do not need an equivalent for 2, since that is captured in is_2
    found_3: bool

    def __init__(self, lo: float, hi: float, err: float = 1.0):
        ''' The range of values to search over. err is the error margin when we
        stop'''
        assert(lo <= hi)
        assert(err > 0)
        self.is_1 = lo
        self.is_2 = None
        self.is_3 = hi
        self.err = err
        self.found_1 = False
        self.found_3 = False

    def next_pt(self) -> Optional[float]:
        ''' The next point we should be searching over. Returns None if we are
        done searching '''

        if not self.found_1:
            return self.is_1
        if not self.found_3:
            return self.is_3

        assert(self.is_1 <= self.is_3)
        if self.is_2 is None:
            if self.is_3 - self.is_1 <= self.err:
                return None
            return (self.is_1 + self.is_3) / 2

        assert(self.is_1 <= self.is_2[0])
        assert(self.is_2[0] <= self.is_2[1])
        assert(self.is_2[1] <= self.is_3)

        # First, we'll search between 1 and 2
        if self.is_2[0] - self.is_1 > self.err:
            return (self.is_1 + self.is_2[0]) / 2
        if self.is_3 - self.is_2[1] > self.err:
            return (self.is_3 + self.is_2[1]) / 2
        return None

    def register_pt(self, pt: float, val: int):
        assert(val in [1, 2, 3])
        assert(pt == self.next_pt())

        if not self.found_1:
            self.found_1 = True
        elif not self.found_3:
            self.found_3 = True

        if val == 1:
            self.found_1 = True
            assert(self.is_1 <= pt)
            self.is_1 = pt
        elif val == 3:
            self.found_3 = True
            assert(self.is_3 >= pt)
            self.is_3 = pt
        elif val == 2:
            if not self.found_1:
                # In case 1 doesn't exist
                self.found_1 = True
            elif not self.found_3:
                # In case 3 doesn't exist
                self.found_3 = True

            if self.is_2 is None:
                self.is_2 = [pt, pt]
            else:
                assert(self.is_2[0] <= self.is_2[1])
                if self.is_2[0] >= pt:
                    self.is_2[0] = pt
                elif self.is_2[1] <= pt:
                    self.is_2[1] = pt
                else:
                    assert(False)

    def get_bounds(self) -> Tuple[float, Optional[Tuple[float, float]], float]:
        assert(self.next_pt() is None)
        if self.is_2 is not None:
            return (self.is_1, (self.is_2[0], self.is_2[1]), self.is_3)
        else:
            return (self.is_1, None, self.is_3)
