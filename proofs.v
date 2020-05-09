Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.

Module CongestionControl.

Local Open Scope list_scope.

(** Currently carries no data. We may augment this wil flow id, 
    sequence number etc. *)
Inductive Packet : Type :=
| packet (seq : nat)
| lost (seq : nat)
| none.

(** Time is represented as a natural number, in 'ticks'. This is not a problem,
    as we can make a tick correspond to an arbitrarily small amount of real 
    time. *)
Definition Time : Type := nat.

(** We often specify a sequence of times as deltas from the previous, 
    rather than specify the absolute time. This representation has 
    three advantages. First, a finite list is easier reason about. 
    Second, times are always increasing (hence using delta). Third, 
    multiple packets may occupy the same time (by setting delta = 0) *)
Definition TimeDelta : Type := nat.

(** Packets and the times at which they arrived/left/enqueued/... someplace. 
    Times are given as a _delta_ in time from the previous packet.*)
Definition PktTrain := list (TimeDelta * Packet).

(** Timestamps at which events happened. Times are given as a _delta_ 
    in time from the previous packet.*)
Definition Events := list TimeDelta.

(** Strips packet information to return just list of times. Useful when
    we only want to reason about timestamps *)
Fixpoint times_only (inp : PktTrain) : Events :=
  match inp with
  | nil => nil
  | (t, _) :: inp' => t :: times_only inp'
  end.

(** Boolean version of In *)
Fixpoint Inb (x : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | a :: l' => if (Nat.eqb x a) then true else (Inb x l')
  end.

Theorem In_Inb_eqiv : forall x l, Inb x l = true <-> In x l.
Proof.
  intros. split.
  - induction l.
    + simpl. intro. inversion H.
    + unfold Inb. remember (Nat.eqb x a) as eqb. destruct eqb.
      * (* true *) intros H'. clear H'. simpl. left. symmetry in Heqeqb.
        apply PeanoNat.Nat.eqb_eq in Heqeqb. symmetry. apply Heqeqb.
      * (* false *)fold Inb. intro H. simpl. right. 
        apply IHl in H. apply H.
  - induction l.
    + simpl. intro H. inversion H.
    + intro H. simpl in H. destruct H.
      * (* a = x *) unfold Inb. symmetry in H. apply PeanoNat.Nat.eqb_eq in H.
        rewrite -> H. reflexivity.
      * (* In x l *) unfold Inb. destruct (Nat.eqb x a); try reflexivity.
        fold Inb. apply IHl. apply H.
Qed.

(** Convert list TimeDelta to list Time with cumulative times *)
Fixpoint time_delta_to_cum' (deltas : list TimeDelta) (cum_time: Time) 
: list Time :=
  match deltas with
  | nil => nil
  | d :: deltas' => (cum_time + d) :: (time_delta_to_cum' deltas' (cum_time+d))
  end.

Definition time_delta_to_cum (deltas : list TimeDelta) : list Time :=
  time_delta_to_cum' deltas 0.

Fixpoint train_delta_to_cum' (train : PktTrain) (cum_time: Time) 
: list (Time * Packet) :=
  match train with
  | nil => nil
  | (d, p) :: train' => 
    (cum_time + d, p) :: (train_delta_to_cum' train' (cum_time + d))
  end.

Definition train_delta_to_cum (train : PktTrain) : list (Time * Packet) :=
  train_delta_to_cum' train 0.


(** Number of events till the given time *)
Fixpoint events_sum_t (t : Time) (opps : list TimeDelta) : nat :=
  match opps with
  | nil => 0
  | t' :: ops' => if (Nat.leb t' t) then S (events_sum_t t ops') else 0
  end.

(** Alternate definition of events_sum_t with cumulative times instead *)
Fixpoint events_sum_t' (t : Time) (times : list Time) : nat :=
  match t with
  | O => if (Inb O times) then 1 else 0
  | S t' => if (Inb (S t') times) then 
            S (events_sum_t' t' times) else
            (events_sum_t' t' times)
  end.

Theorem events_sum_t_eqiv : forall t opps,
  events_sum_t t opps = events_sum_t' t (time_delta_to_cum opps).
Proof.
  intros t opps.
  Admitted.

(** The notion of a PacketTrain whose rate is fixed with some upper and
    lower slack *)
Definition RateBoundedEvents (inter_packet uslack lslack : nat) 
(events : Events) : Prop :=
  forall t,
  ((events_sum_t t events) - uslack) * inter_packet <= t /\
  ((events_sum_t t events) + lslack) * inter_packet >= t.


(** This is how we define how a network component modifies 
    (delays/drops) packets *)
Definition NetworkComponent := PktTrain -> PktTrain.

(** Define an infinite buffer link w.r.t a set of transmit opps *)
Variable link_inf : list TimeDelta -> NetworkComponent.
(** Conditions for a packet to be output by a link_inf *)
Axiom link_inf_cond : 
    forall inp : PktTrain,
    forall opps : list TimeDelta,
    forall t out,
    out = (link_inf opps inp) ->
    ((In t (time_delta_to_cum (times_only out))) <->
    (
      (* Queue is non-empty *)
      (events_sum_t t (times_only out)) < (events_sum_t t (times_only inp)) /\
      (* There was a transmit opportunity at that time *)
      (In t (time_delta_to_cum opps))
    )).

(** Prove how LinkInf affects bounds of an incoming RateBoundedEvents
    of packets *)
Theorem link_inf_bounds : 
forall inp opps,
forall inter_packet l_uslack l_lslack i_uslack i_lslack,
RateBoundedEvents inter_packet i_uslack i_lslack (times_only inp) ->
RateBoundedEvents inter_packet l_uslack l_lslack opps ->
RateBoundedEvents inter_packet i_uslack (i_lslack + 2 * l_lslack) 
  (times_only (link_inf opps inp)).
Proof.
  intros inp opps inter_packet l_uslack l_lslack i_uslack i_lslack Hinp Hopps.
  split.
  - (* uslack doesn't change *)
    remember (link_inf opps inp) as out.
    (* pose link_inf_cond as Hlink. specialize (Hlink inp opps t out).
    apply Hlink in Heqout. clear Hlink. rename Heqout into Hlink. *)

    (* This gives us the theorem when t is in out. We need to
       handle the other case as well *)
     
    (* If t is not in out, then the sum is the same as for t-1 *)
    assert (forall t, ~(In (S t) (time_delta_to_cum (times_only out))) ->
      events_sum_t (S t) (times_only out) = events_sum_t t (times_only out)) as Hp. {
      intros t' H.
      repeat rewrite -> events_sum_t_eqiv.
      unfold events_sum_t'.
      assert (Inb (S t') (time_delta_to_cum (times_only out)) = false) as Hf. {
        rewrite <- In_Inb_eqiv in H. 
        (* Prove x <> true implies x = false *)
        destruct (Inb (S t') (time_delta_to_cum (times_only out))).
        - unfold not in H. assert (true = true). { reflexivity. } apply H in H0.
          inversion H0.
        - reflexivity.
      }
      rewrite Hf. fold events_sum_t'. reflexivity.
    }

    (* This gives us the theorem when t is in out. To handle other times,
       we'll use induction on t. *)
    elim t. (* NOTE: Don't understand what the induction tactic does here *)
    + admit.
    + intros n H.
      pose link_inf_cond as Hlink. specialize (Hlink inp opps (S n) out).
      apply Hlink in Heqout. clear Hlink. rename Heqout into Hlink.
      (* This gives us the theorem when t is in out. We used induction
         to handle the other case as well *)
      (* Use excluded middle to handle two cases *)
      pose classic as Hin. 
      specialize (Hin (In (S n) (time_delta_to_cum (times_only out)))).
      destruct Hin as [Hin|Hnotin].

      * (* (S n) is in out *)
        apply Hlink in Hin. destruct Hin as [Hle _].
        (* Use Hle and Hinp together *)
        unfold RateBoundedEvents in Hinp. specialize (Hinp (S n)). 
        destruct Hinp as [Hinp _].
        Search le.
        apply PeanoNat.Nat.le_trans with 
          (m:=(events_sum_t (S n) (times_only inp) - i_uslack) * inter_packet).
        -- apply PeanoNat.Nat.mul_le_mono_nonneg_r. apply le_0_n.
          apply PeanoNat.Nat.sub_le_mono_r. apply PeanoNat.Nat.lt_le_incl.
          apply Hle.
        -- apply Hinp.
      * (* (S n) is not in out *)
        specialize (Hp n). apply Hp in Hnotin. rewrite Hnotin.
        apply le_S. apply H.
Admitted.


(** Define a non-deterministic finite buffered link based on TOps. It
    first enqueues packet from input then dequeues them if tops demands
    it *)
Fixpoint nd_link' (opps : list TimeDelta) (input : PktTrain) 
(buf : list Packet) (in_time opp_time: Time) (opp_delta_acc: TimeDelta) 
: PktTrain :=
(* buf queue outputs packets at the head and inputs from the tail *)
  match (input, opps) with
  | ([], []) => []
  | ((in_delta, in_pkt) :: input', []) => []
  | ([], opp_delta :: opps') => []
  | ((in_delta, in_pkt) :: input', opp_delta :: opps') =>
    if (Nat.leb (in_time + in_delta) (opp_time + opp_delta)) then
      (nd_link' opps input' (app buf (cons in_pkt nil)) (in_time + in_delta) 
        opp_time opp_delta_acc) else
      ((opp_delta_acc + opp_delta, (hd [] buf)) ::
        (nd_link' opps' input (tl buf) in_time (opp_time + opp_delta) 0))
  end.

  match input with
  | nil => match opps with
    | nil => nil
    | opp_delta :: opps' => match buf with
      | nil => nil
      | buf_pkt :: buf' => 
          (opp_delta_acc + opp_delta, buf_pkt) :: 
           (nd_link' opps' input buf' in_time (opp_time + opp_delta) 0)
      end
    end
  | (in_delta, in_pkt) :: input' => match opps with
    | nil => nil
    | opp_delta :: opps' => match buf with
      | nil => nil
      | buf_pkt :: buf' =>
          if (Nat.leb (in_time + in_delta) (opp_time + opp_delta)) then
          (nd_link' opps input' (app buf (cons in_pkt nil)) (in_time + in_delta) 
            opp_time opp_delta_acc) else
          (opp_delta_acc + opp_delta, buf_pkt) :: 
            (nd_link' opps' input buf' in_time (opp_time + opp_delta) 0)
      end
    end
  end.


End CongestionControl.