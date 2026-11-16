From Stdlib Require Import QArith Qabs Psatz Lia.
Open Scope Q_scope.

Lemma rational_scalar_signed_square (s w h b : Q)
    (Hw : 0 <= w) (Hb : 0 <= b)
    (Hh : Qabs h <= b) (Hs : Qabs s <= 1) :
    Qabs (s * w * (h * h)) <= w * (b * b).
Proof.
  apply Qabs_Qle_condition in Hh.
  apply Qabs_Qle_condition in Hs.
  apply Qabs_Qle_condition.
  assert (Hsq : h * h <= b * b) by nra.
  assert (Hpos : 0 <= h * h) by nra.
  assert (Hwh : 0 <= w * (h * h)).
  { apply Qmult_le_0_compat; assumption. }
  assert (Hweighted : w * (h * h) <= w * (b * b)).
  { setoid_replace (w * (h * h)) with ((h * h) * w) by ring.
    setoid_replace (w * (b * b)) with ((b * b) * w) by ring.
    apply Qmult_le_compat_r; assumption. }
  pose proof (Qmult_le_compat_r _ _ _ (proj1 Hs) Hwh) as Hlower.
  pose proof (Qmult_le_compat_r _ _ _ (proj2 Hs) Hwh) as Hupper.
  split; nra.
Qed.

Fixpoint qprefixSum (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => qprefixSum f k + f k
  end.

Theorem rational_signed_square_envelope :
  forall (n : nat) (s w h b : nat -> Q),
    (forall i, (i < n)%nat -> 0 <= w i) ->
    (forall i, (i < n)%nat -> 0 <= b i) ->
    (forall i, (i < n)%nat -> Qabs (h i) <= b i) ->
    (forall i, (i < n)%nat -> Qabs (s i) <= 1) ->
    Qabs (qprefixSum (fun i => s i * w i * (h i * h i)) n) <=
      qprefixSum (fun i => w i * (b i * b i)) n.
Proof.
  induction n as [| n IH]; intros s w h b Hw Hb Hh Hs.
  - change (0 <= 0). apply Qle_refl.
  - cbn [qprefixSum].
    eapply Qle_trans; [apply Qabs_triangle |].
    apply Qplus_le_compat.
    + apply IH; intros i Hi.
      * apply Hw. lia.
      * apply Hb. lia.
      * apply Hh. lia.
      * apply Hs. lia.
    + apply rational_scalar_signed_square.
      * apply Hw. lia.
      * apply Hb. lia.
      * apply Hh. lia.
      * apply Hs. lia.
Qed.

Theorem rational_missing_sign_bound_counterexample :
  0 <= (1 : Q) /\ 0 <= (1 : Q) /\ Qabs 1 <= 1 /\
  ~ (Qabs (2 * 1 * (1 * 1)) <= 1 * (1 * 1)).
Proof. vm_compute. intuition congruence. Qed.

Print Assumptions rational_scalar_signed_square.
Print Assumptions rational_signed_square_envelope.
Print Assumptions rational_missing_sign_bound_counterexample.
