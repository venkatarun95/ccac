predicate sorted(s: seq<real>)
{
    forall j, k :: 0 <= j <= k < |s| ==> s[j] <= s[k] 
}

predicate bounded_topps(opps: seq<real>, C: real, ku: real, kl: real)
{
    sorted(opps) && 
    forall t :: 0 <= t < |opps| ==> t as real * C - kl <= opps[t] <= t as real * C + ku
}

/*lemma LemmaBoundedToppsConcat(opps1: seq<real>, opps2: seq<real>, C: real, ku: real, kl: real)
decreases opps1
requires bounded_topps(opps1, C, ku, kl)
requires bounded_topps(opps2, C, ku, kl)
ensures bounded_topps(opps1 + seq_add(opps2, C * |opps1| as real), C, ku, kl)
{
    if |opps1| == 0 {
        assert seq_add(opps2, 0.0) == opps2;
        assert opps1 + seq_add(opps2, C * |opps1| as real) == opps2;
    } else {

        var x := C * |opps1| as real;
        assert seq_add([opps1[|opps1|-1] - x] + opps2, x) == [opps1[|opps1|-1]] + seq_add(opps2, x);
        assert opps1 + seq_add(opps2, C * |opps1| as real) ==
            opps1[..|opps1|-1] + seq_add([opps1[|opps1|-1] - x] + opps2, x);
        LemmaBoundedToppsConcat(opps1[..|opps1|-1], [opps1[|opps1|-1] - x] + opps2, C, ku, kl);
    }
}*/

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

// A constant bit rate link
/*method link_cbr(C: real, t: nat) returns (opps: seq<real>)
    requires C > 0.0
    ensures sorted(opps)
    ensures forall ku, kl :: && 0.0 <= ku && 0.0 <= kl ==> bounded_topps(opps, C, ku, kl)
{
    if t == 0 {
        return [];
    }
    var tail := link_cbr(C, t-1);
    return [0.0] + seq_add(tail, C);
}*/

method link_cbr(inp: seq<real>, C: real) returns (out: seq<real>)
    requires sorted(inp)
    requires |inp| == 0 || inp[0] >= 0.0
    requires C > 0.0
    ensures bounded_topps(out, C, 0.0, 0.0)
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