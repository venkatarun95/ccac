predicate sorted(s: seq<real>)
{
    forall j, k :: 0 <= j <= k < |s| ==> s[j] <= s[k] 
}

// If all neighbors are in sorted order, 'sorted' is true
lemma SortedNeighbor(s: seq<real>)
requires forall i :: 0 <= i < i + 1 < |s| ==> s[i] <= s[i+1]
ensures sorted(s)
{
    forall j, k | 0 <= j <= k < |s| {
        SortedNeighborHelper(s, j, k);
    }
}

lemma SortedNeighborHelper(s: seq<real>, j: nat, k: nat)
requires forall i :: 0 <= i < i + 1 < |s| ==> s[i] <= s[i+1]
requires 0 <= j <= k < |s|
ensures s[j] <= s[k] {
    var i := j;
    while i < k 
    invariant 0 <= j <= i <= k <= |s|
    invariant s[j] <= s[i]
    {
        i := i + 1;
    }
}

predicate bounded_topps(opps: seq<real>, C: real, ku: real, kl: real)
{
    sorted(opps) && 
    forall t :: 0 <= t < |opps| ==> t as real * C - kl <= opps[t] <= t as real * C + ku
}

function run_inf_link(inp: seq<real>, opps: seq<real>) : (out: seq<real>)
requires sorted(inp)
requires sorted(opps)
{}

// Definition of a link with an infinitely large buffer
/*method run_inf_link(inp: array<int>, opps: array<int>) returns (out: array<int>) 
requires inp.Length == opps.Length
requires sorted(inp)
requires sorted(out)
{
    var t := 1;
    var queue_len := if inp[0] > opps[0] then {
        inp[0] - opps[0]
    } else {
        0
    };

    while t < inp.Length || queue_len > 0 
    invariant queue_len >= 0
    {
        queue_len := queue_len + inp[t] - inp[t-1];
        var change := if queue_len > (out[t] - out[t-1]) then {
            out[t] - out[t-1]
        } else {
            queue_len
        };
        queue_len := queue_len - change;
        t := t + 1;
    }
    return out;
}*/

// Add a constant to a sequence
function method seq_add(inp: seq<real>, val: real) : (out: seq<real>)
ensures |inp| == |out|
decreases |inp|
ensures forall i :: 0 <= i < |inp| ==> inp[i] + val == out[i]
{
    if |inp| == 0 then
        []
    else if |inp| == 1 then
        [inp[0] + val]
    else
        [inp[0] + val] + seq_add(inp[1..], val)
}

method link_cbr(inp: seq<real>, C: real) returns (opps: seq<real>)
    requires sorted(inp)
    requires |inp| > 0 ==> inp[0] >= 0.0
    requires C > 0.0
    ensures bounded_topps(opps, C, 0.0, 0.0)
{
    if |inp| == 0 {
        return [];
    }

    var t: nat := 1;
    var tot_timesteps := 0;
    var queue := inp[0];
    assert queue >= 0.0;

    while t < |inp|
    decreases |inp| - t, queue 
    invariant 0 <= t <= |inp|
    invariant queue >= 0.0
    {
        if t < |inp| {
            queue := queue + inp[t] - inp[t-1];
            t := t + 1;
        }
        assert C >= 0.0;
        queue := if queue < C then 0.0 else queue - C;

        tot_timesteps := tot_timesteps + 1;
    }


    // After the input is finished, clear the queue
    assert queue / C >= 0.0;
    tot_timesteps := tot_timesteps + (queue / C + 1.0).Floor;
    assert tot_timesteps >= 0;

    // Generate the sequence of the appropriate length and return
    var res := new real[tot_timesteps];
    forall t | 0 <= t < tot_timesteps
    {
        res[t] := t as real * C;
    }
    return res[..];
}

// Implements a link of the given rate that sends a burst every 
// 'agg' timesteps
method link_aggr(tot_timesteps: nat, C: real, agg: nat) returns (opps: seq<real>)
requires agg > 0
requires C > 0.0
ensures bounded_topps(opps, C, 0.0, C  * agg as real)
{
    var res := new real[tot_timesteps];
    var t := 0;
    while t < tot_timesteps 
    invariant 0 <= t <= tot_timesteps
    invariant forall i :: 0 <= i < t ==> res[i] == C * ((i / agg) * agg) as real
    {
        res[t] := C * ((t / agg) * agg) as real;
        t := t + 1;
    }

    opps := res[..];

    // Prove that it is sorted
    forall t | 0 <= t < t + 1 < |opps| 
    ensures opps[t] <= opps[t+1];
    {
        assert t <= t + 1;
        assert t / agg <= (t + 1) / agg;
        assert agg > 0;
        assert (t / agg) * agg <= ((t+1) / agg) * agg;
    }
    SortedNeighbor(opps);
    assert sorted(opps);

    return opps;
}