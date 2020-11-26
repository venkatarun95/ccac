method link_aggr(C: real, agg: int) returns (opps: seq<real>)
requires agg > 0
requires C > 0.0
{
    var tot_timesteps := 10;

    var res := new real[tot_timesteps];
    var t := 0;
    while t < tot_timesteps 
    invariant 0 <= t <= tot_timesteps
    invariant forall i :: 0 <= i < t ==> res[i] == C * ((i / agg) * agg) as real
    {
        res[t] := C * ((t / agg) * agg) as real;
        t := t + 1;
    }

    // Prove it fits within the bounds
    forall t | 0 <= t < tot_timesteps 
    ensures res[t] <= C * t as real
    ensures res[t] > C * t as real - C * agg as real
    {
        assert res[t] == C * ((t / agg) * agg) as real;
    }
    opps := res[..];

    // Prove that it is sorted
    forall t | 0 <= t < t + 1 < |opps| 
    ensures opps[t] <= opps[t+1];
    {
        assert t <= t + 1;
        assert t / agg <= (t + 1) / agg;
        assert (t / agg) * agg <= ((t+1) / agg) * agg;
    }
}