Require Import Coq.Arith.PeanoNat.
Require Import Psatz.

Module CongestionControl.
  (** Time is represented as a natural number, in 'ticks'. This is not a problem,
    as we can make a tick correspond to an arbitrarily small amount of real 
    time. *)
  Definition Time := nat.

  (** Units of data (e.g. bytes) *)
  Definition Bytes := nat.

  (** Units of data transmitted per unit time *)
  Definition Rate := nat.

  (** The assertion that f is non-decreasing *)
  Definition monotone (f : (Time -> Bytes)) : Prop :=
    forall t1 t2, t1 < t2 -> (f t1) <= (f t2).

  (** A trace of what the server did and how much input it got *)
  Record Trace : Set := mkTrace {
    (* Parameters of the link *)
    C : Rate;
    K : Bytes;

    (* Data comprising the trace *)
    wasted : Time -> Bytes;
    out : Time -> Bytes;
    inp : Time -> Bytes;

    (* Constraints on out *)
    constraint_u : forall t, (out t) + (wasted t) <= C * t;
    constraint_l : forall t, (out t) + (wasted t) >= C * t - K;

    (* The server can waste transmission opportunities if inp <= upper *)
    cond_waste : forall t, (wasted t) < (wasted (S t)) -> (inp (S t)) + (wasted (S t)) <= C * S t;

    (* Can't output more bytes that we got *)
    out_le_inp : forall t, out t <= inp t;

    (* Everything should be monotonic (non-decreasing) *)
    monotone_wasted : monotone wasted;
    monotone_out : monotone out;
    monotone_inp : monotone inp;

    (* Where everything starts *)
    zero_wasted : wasted 0 = 0;
    zero_out : out 0 = 0;
    zero_inp : inp 0 = 0;
  }.

  Theorem trace_composes :
    forall (s1 s2 : Trace),
      (C s1) = (C s2) /\
      (inp s2) = (out s1) ->
    exists (sc : Trace),
        (K sc) = (K s1) + (K s2) /\
        (C sc) = (C s1) /\
        (inp sc) = (inp s1) /\
        (out sc) = (out s2)
  .
  Proof.
    intros s1 s2 [Hc12 H12].

    (* Note: We will set (wasted sc) = (wasted s1) *)

    (* Prove constraint_u *)
    assert (forall t, (out s2 t) + (wasted s1 t) <= (C s1) * t) as H_eg_constraint_u. {
      intro t.
      (* Proof: (out s2 t) <= (inp s2 t) = (out s1 t) *)
      apply Nat.le_trans with (m:=(inp s2 t)  + (wasted s1 t)).
      apply Nat.add_le_mono_r. apply (out_le_inp s2).
      rewrite H12.
      apply (constraint_u s1).
    }

    (* Intuition: upper of s2 >= lower of s1. This is equivalent to the following *)
    assert (forall t, wasted s2 t <= wasted s1 t + K s1) as H_s2_upper_ge_s1_lower. {
      intro t. induction t.
      - rewrite (zero_wasted s2). rewrite (zero_wasted s1). apply Nat.le_0_l.
      - pose Nat.lt_trichotomy as Hcases. specialize (Hcases (wasted s2 t) (wasted s2 (S t))).
        destruct Hcases as [Hgt|Heq_gt].
        + (* Case: (wasted s2) increased *)
          apply (cond_waste s2) in Hgt.
          rewrite H12 in Hgt.
          assert ((C s1) * (S t) - (K s1) - (wasted s1 (S t)) <= (out s1 (S t))) as H1. {
            apply Nat.le_sub_le_add_r with (p:=(wasted s1 (S t))).
            apply (constraint_l s1).
          }
          lia.
        + destruct Heq_gt as [Heq|Hlt].
          * (* Case: (wasted s2) remains constant *)
            (* (wasted s1) is monotonic *)
            pose (monotone_wasted s1) as H1. unfold monotone in H1.
            specialize (H1 t (S t)). assert (t < S t) as Hmon. { lia. } apply H1 in Hmon.
            rewrite <- Heq.
            lia.
          * (* Case: (wasted s2) decreases, but this cannot happen *)
            exfalso.
            (* (wasted s2) is monotonic *)
            pose (monotone_wasted s2) as H1. unfold monotone in H1.
            specialize (H1 t (S t)). assert (t < S t) as Hmon. { lia. } apply H1 in Hmon.
            lia.
    }

    (* prove constraint_l *)
    assert (forall t, (out s2 t) + (wasted s1 t) >= (C s1) * t - (K s1 + K s2)) as H_eg_constraint_l. {
      intro t. specialize (H_s2_upper_ge_s1_lower t).
      pose (constraint_l s2) as Hl2. specialize (Hl2 t).
      lia.
    }

    (* cond_waste is the same as for s1. Hence no need to prove *)

    (* prove out_le_inp *)
    assert (forall t, out s2 t <= inp s1 t) as H_eg_out_le_inp. {
      intro t.
      pose (out_le_inp s1) as Hs1. specialize (Hs1 t).
      pose (out_le_inp s2) as Hs2. specialize (Hs2 t).
      rewrite H12 in Hs2.
      apply Nat.le_trans with (m:=(out s1 t)); assumption.
    }

    (* Now we are ready to construct our example *)
    remember (mkTrace
                (C s1)
                (K s1 + K s2)
                (wasted s1)
                (out s2)
                (inp s1)
                H_eg_constraint_u
                H_eg_constraint_l
                (cond_waste s1)
                H_eg_out_le_inp
                (monotone_wasted s1)
                (monotone_out s2)
                (monotone_inp s1)
                (zero_wasted s1)
                (zero_out s2)
                (zero_inp s1)
             ) as example.

    (* Show example has the required properties *)
    exists example.
    repeat split; rewrite Heqexample; reflexivity.
  Qed.
End CongestionControl.
