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
    (* Minimum buffer size *)
    Buf : Bytes;

    (* Data comprising the trace *)
    (* Upper limit is C * t - wasted t. Lower limit is (upper limit - K) *)
    wasted : Time -> Bytes;
    out : Time -> Bytes;
    lost : Time -> Bytes;
    (* Number of bytes that have come in (irrespective of whether they were lost) *)
    inp : Time -> Bytes;
    (* Packets can be lost if inp t >= C * t - loss_thresh t*)
    loss_thresh : Time -> Bytes;

    (* Constraints on out *)
    constraint_u : forall t, (out t) + (wasted t) <= C * t;
    constraint_l : forall t, (out t) + (wasted t) >= C * t - K;

    (* The server can waste transmission opportunities if inp <= upper *)
    cond_waste : forall t, wasted t < wasted (S t) ->
                           inp (S t) - lost (S t) + wasted (S t) <= C * S t;

    (* Can only lose packets if packets in queue > C * t - loss_thresh t *)
    cond_lost : forall t, lost t < lost (S t) ->
                          C * (S t) - loss_thresh (S t) < inp (S t) - lost (S t);

    (* loss_thresh increases whenever queue length is 0. Note: what happens in
       (S t) is determined by variables in t *)
     cond_loss_thresh : forall t, loss_thresh t < loss_thresh (S t) ->
                                 out t = inp t - lost t /\
                                 C * (S t) - loss_thresh (S t) = out t + Buf + C;

    (* Can't output more bytes that we got *)
    out_le_inp : forall t, out t <= inp t - lost t;

    (* Everything should be monotonic (non-decreasing) *)
    monotone_wasted : monotone wasted;
    monotone_out : monotone out;
    monotone_lost : monotone lost;
    monotone_inp : monotone inp;
    monotone_loss_thresh : monotone loss_thresh;

    (* Where everything starts *)
    zero_wasted : wasted 0 = 0;
    zero_out : out 0 = 0;
    zero_lost : lost 0 = 0;
    zero_inp : inp 0 = 0;
    zero_loss_thresh : loss_thresh 0 = 0;
  }.

  (** If the buffer of a latter link is bigger than the K of the preceeding
  link, the latter link cannot drop packets. *)
  Theorem trace_no_subsequent_loss :
    forall (s1 s2 : Trace),
      (C s1) = (C s2) /\
      (inp s2) = (out s1) /\
      (K s1) < (Buf s2) ->
      forall t, (lost s2 t) = 0.
  Proof.
    intros s1 s2 [Hc12 [H12 Hbuf_K]] t.

    (* Expand the goal to prove with a new condition. This will help with induction *)
    assert (wasted s1 t >= loss_thresh s2 t /\
            lost s2 t = 0 -> lost s2 t = 0) as H.
    { intro. destruct H. apply H0. }
    apply H. clear H.

    induction t.
    - rewrite (zero_loss_thresh s2). rewrite (zero_lost s2). lia.
    - (* Split IHt *)
      destruct IHt as [IHt_upper IHt_lost].
      (* Assert the first part of the induction separately, so we can use it later *)
      assert (wasted s1 (S t) >= loss_thresh s2 (S t)) as IHSt_upper. {
        (* Prove some monotonicity theorems for convenience *)
        pose (monotone_wasted s1) as Htmp. specialize (Htmp t (S t)).
        assert (t < S t) as HWmon. auto. apply Htmp in HWmon. clear Htmp.
        pose (monotone_inp s2) as Htmp. specialize (Htmp t (S t)).
        assert (t < S t) as HImon. auto. apply Htmp in HImon. clear Htmp.

        (* Create cases: either loss_thresh increased or it didn't *)
        remember (loss_thresh s2 (S t) - loss_thresh s2 t) as incr.
        destruct incr.
        * (* loss_thresh didn't increase *)
          assert (loss_thresh s2 (S t) = loss_thresh s2 t). {
            pose (monotone_loss_thresh s2) as Hm. specialize (Hm t (S t)).
            assert (t < S t) as Htmp. auto. apply Hm in Htmp. lia.
          }
          rewrite H.
          lia.
        * (* loss_thresh increased. So use cond_loss_thresh *)
          assert (loss_thresh s2 t < loss_thresh s2 (S t)) as Hincr. lia.
          clear Heqincr.

          apply (cond_loss_thresh s2) in Hincr. destruct Hincr as [Hempty Hthresh].
          pose (constraint_l s1 t) as Hls1. rewrite <- H12 in Hls1. rewrite Hc12 in Hls1.

          lia.
      }

      split.
      + (* We already proves this above *) assumption.
      + (* Create cases: either lost increased or it didn't *)
        remember (lost s2 (S t)) as lost_s2_St.
        destruct lost_s2_St. reflexivity.
        exfalso.
        assert (lost s2 (S t) > 0) as H_gt_0. lia.
        clear Heqlost_s2_St. clear lost_s2_St.

        (* If lost increased, packets in queue must have increased the threshold
           (C * t - loss_thresh t) *)
        rewrite <- IHt_lost in H_gt_0.
        apply (cond_lost s2) in H_gt_0.

        assert (C s2 * S t - loss_thresh s2 (S t) >= inp s2 (S t) - lost s2 (S t)). {
          rewrite H12.
          pose (constraint_u s1 (S t)) as Hu. lia.
        }

        (* Exploit contradiction *)
        lia.
  Qed.



  Theorem trace_composes :
    forall (s1 s2 : Trace),
      (C s1) = (C s2) /\
      (inp s2) = (out s1) /\
      (K s1) < (Buf s2) ->
    exists (sc : Trace),
        (K sc) = (K s1) + (K s2) /\
        (C sc) = (C s1) /\
        (Buf sc) = (Buf s1) /\
        (inp sc) = (inp s1) /\
        (out sc) = (out s2) /\
        forall t, (lost sc t) = (lost s1 t) + (lost s2 t)
  .
  Proof.
    intros s1 s2 [Hc12 [H12 HKBuf]].

    (* Note: We will set (wasted sc) = (wasted s1) and (lost sc) = (lost s1) *)

    (* Prove constraint_u *)
    assert (forall t, (out s2 t) + (wasted s1 t) <= (C s1) * t) as H_eg_constraint_u. {
      intro t.
      (* Proof: (out s2 t) <= (inp s2 t) - (lost s2 t) <= (inp s2 t) = (out s1 t) *)
      apply Nat.le_trans with (m:=(inp s2 t)  + (wasted s1 t)).
      apply Nat.add_le_mono_r.
      apply Nat.le_trans with (m:=(inp s2 t) - (lost s2 t)). apply (out_le_inp s2).
      apply Nat.le_sub_l.
      rewrite H12.
      apply (constraint_u s1).
    }

    (* Apply trace_no_subsequent_loss and keep for future use *)
    assert (forall t, lost s2 t = 0) as Hloss2. {
      apply trace_no_subsequent_loss with (s1:=s1). repeat split; assumption.
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
          rewrite (Hloss2 (S t)) in Hgt.
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
    assert (forall t, out s2 t <= inp s1 t - (lost s1 t + lost s2 t)) as H_eg_out_le_inp. {
      intro t.
      pose (out_le_inp s1) as Hs1. specialize (Hs1 t).
      pose (out_le_inp s2) as Hs2. specialize (Hs2 t).
      rewrite H12 in Hs2.
      rewrite (Hloss2 t) in Hs2. rewrite Nat.sub_0_r in Hs2.
      rewrite (Hloss2 t). rewrite Nat.add_0_r.
      apply Nat.le_trans with (m:=(out s1 t)); assumption.
    }

    (* Now we are ready to construct our example *)
    remember (mkTrace
                (C s1)
                (K s1 + K s2)
                (wasted s1)
                (out s2)
                (lost s1)
                (inp s1)
                (loss_thresh s1)
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
