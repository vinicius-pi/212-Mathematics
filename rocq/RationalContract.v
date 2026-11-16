From Stdlib Require Import QArith Qabs Psatz Lia.
Require Import RationalEnvelope.
Open Scope Q_scope.

Definition qabs (x : Q) : Q := if Qlt_le_dec x 0 then -x else x.

Lemma qabs_matches_Qabs (x : Q) : qabs x == Qabs x.
Proof.
  unfold qabs. destruct (Qlt_le_dec x 0) as [Hneg | Hnonneg].
  - symmetry. apply Qabs_neg. lra.
  - symmetry. apply Qabs_pos. exact Hnonneg.
Qed.

Lemma square_is_power_two (x : Q) : x ^ 2 == x * x.
Proof. ring. Qed.

Lemma qprefixSum_ext (n : nat) (f g : nat -> Q) :
  (forall i, (i < n)%nat -> f i == g i) ->
  qprefixSum f n == qprefixSum g n.
Proof.
  induction n as [| n IH]; intro H.
  - reflexivity.
  - cbn [qprefixSum]. apply Qplus_comp.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

Theorem signed_square_envelope (n : nat) (s w h b : nat -> Q)
    (Hw : forall i, (i < n)%nat -> 0 <= w i)
    (Hb : forall i, (i < n)%nat -> 0 <= b i)
    (Hh : forall i, (i < n)%nat -> qabs (h i) <= b i)
    (Hs : forall i, (i < n)%nat -> qabs (s i) <= 1) :
  qabs (qprefixSum (fun i => s i * w i * h i ^ 2) n) <=
    qprefixSum (fun i => w i * b i ^ 2) n.
Proof.
  setoid_rewrite qabs_matches_Qabs.
  assert (Hleft :
    qprefixSum (fun i => s i * w i * h i ^ 2) n ==
    qprefixSum (fun i => s i * w i * (h i * h i)) n).
  { apply qprefixSum_ext. intros i Hi. ring. }
  assert (Hright :
    qprefixSum (fun i => w i * b i ^ 2) n ==
    qprefixSum (fun i => w i * (b i * b i)) n).
  { apply qprefixSum_ext. intros i Hi. ring. }
  setoid_rewrite Hleft. setoid_rewrite Hright.
  apply rational_signed_square_envelope; try assumption.
  - intros i Hi. specialize (Hh i Hi).
    setoid_rewrite qabs_matches_Qabs in Hh. exact Hh.
  - intros i Hi. specialize (Hs i Hi).
    setoid_rewrite qabs_matches_Qabs in Hs. exact Hs.
Qed.

Print Assumptions signed_square_envelope.
