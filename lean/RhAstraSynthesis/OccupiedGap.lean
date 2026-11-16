import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Occupied reciprocal gaps yield distinct critical points

Source obligation: GEVREY_BAD_SET_PROOF_SPEC.md, steps 2 and 3.
This module does not assume the bad-set measure bound.
The measure covering and largest-gap summation remain separate obligations.
-/

namespace RhAstraSynthesis

open Set

/-- An overshoot between two good endpoints forces an interior critical point.
The witness is a maximum of the square, so both signs of the overshoot are covered. -/
theorem interval_overshoot_has_derivative_root
    (P : Polynomial ℝ) (a b B t : ℝ)
    (hB : 0 < B) (ht : t ∈ Ioo a b)
    (ha : |P.eval a| ≤ B) (hb : |P.eval b| ≤ B)
    (hbad : B < |P.eval t|) :
    ∃ c ∈ Ioo a b, P.derivative.eval c = 0 := by
  have haSq : (P.eval a)^2 ≤ B^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (P.eval a)) hB.le).2 ha
  have hbSq : (P.eval b)^2 ≤ B^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (P.eval b)) hB.le).2 hb
  have htSq : B^2 < (P.eval t)^2 := by
    simpa only [sq_abs] using
      (sq_lt_sq₀ hB.le (abs_nonneg (P.eval t))).2 hbad
  obtain ⟨c, hc, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (show (Icc a b).Nonempty from ⟨t, ht.1.le, ht.2.le⟩)
      (P.continuous.pow 2).continuousOn
  have hcSq : B^2 < (P.eval c)^2 :=
    lt_of_lt_of_le htSq (hmax ⟨ht.1.le, ht.2.le⟩)
  have hca : a < c := by
    by_contra h
    have hce : c = a := le_antisymm (le_of_not_gt h) hc.1
    subst c
    linarith
  have hcb : c < b := by
    by_contra h
    have hce : c = b := le_antisymm hc.2 (le_of_not_gt h)
    subst c
    linarith
  have hcP : P.eval c ≠ 0 := by
    intro hz
    rw [hz] at hcSq
    nlinarith [sq_nonneg B]
  have hd : 2 * P.eval c * P.derivative.eval c = 0 := by
    simpa using
      (hmax.isLocalMax (Icc_mem_nhds hca hcb)).hasDerivAt_eq_zero
        ((P.hasDerivAt c).pow 2)
  exact ⟨c, ⟨hca, hcb⟩,
    (mul_eq_zero.mp hd).resolve_left (mul_ne_zero (by norm_num) hcP)⟩

/-- The actual reciprocal-gap instance: no measure bound is assumed. -/
theorem occupied_gap_has_derivative_root
    (P : Polynomial ℝ) (B : ℝ) (j : ℕ) (hB : 0 < B)
    (ha : |P.eval (1 / (↑(j+1) : ℝ))| ≤ B)
    (hb : |P.eval (1 / (j : ℝ))| ≤ B)
    (hbad : ∃ t ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)),
      B < |P.eval t|) :
    ∃ c ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)),
      P.derivative.eval c = 0 := by
  obtain ⟨t, ht, htB⟩ := hbad
  exact interval_overshoot_has_derivative_root P _ _ B t hB ht ha hb htB

/-- A point belongs to at most one positive-index reciprocal open gap. -/
theorem reciprocal_gap_index_unique
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (x : ℝ)
    (hxi : x ∈ Ioo (1 / (↑(i+1) : ℝ)) (1 / (i : ℝ)))
    (hxj : x ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ))) :
    i = j := by
  have ordered (u v : ℕ) (huv : u < v) :
      (1 : ℝ) / (v : ℝ) ≤ 1 / (↑(u+1) : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (Nat.succ_le_iff.mpr huv)
  rcases lt_trichotomy i j with hij | hij | hji
  · have h := ordered i j hij
    linarith [hxi.1, hxj.2]
  · exact hij
  · have h := ordered j i hji
    linarith [hxj.1, hxi.2]

#print axioms interval_overshoot_has_derivative_root
#print axioms occupied_gap_has_derivative_root
#print axioms reciprocal_gap_index_unique

/-- Every finite family of occupied positive-index gaps has at most
deg(P)-1 members. The constant case is included, rather than hidden
behind an assumption that the derivative is nonzero. -/
theorem occupied_gaps_finset_card_le
    (P : Polynomial ℝ) (B : ℝ) (hB : 0 < B)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B)
    (S : Finset ℕ)
    (hS : ∀ j ∈ S, 0 < j ∧
      ∃ t ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)),
        B < |P.eval t|) :
    S.card ≤ P.natDegree - 1 := by
  classical
  by_cases hp : P.derivative = 0
  · have hconst := Polynomial.eq_C_of_derivative_eq_zero hp
    have heval (x : ℝ) : P.eval x = P.coeff 0 := by
      have h := congrArg (fun Q : Polynomial ℝ => Q.eval x) hconst
      simpa only [Polynomial.eval_C] using h
    have hbound : |P.coeff 0| ≤ B := by
      simpa only [heval] using hsample 1 (by omega)
    have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨_, t, _, ht⟩ := hS j hj
      have : B < |P.coeff 0| := by
        simpa only [heval] using ht
      linarith
    simp [hempty]
  · have hex (j : ℕ) (hj : j ∈ S) :
        ∃ c ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)),
          P.derivative.eval c = 0 :=
      occupied_gap_has_derivative_root P B j hB
        (hsample (j+1) (by omega)) (hsample j (hS j hj).1) (hS j hj).2
    let c : ℕ → ℝ := fun j =>
      if hj : j ∈ S then Classical.choose (hex j hj) else 0
    have hc (j : ℕ) (hj : j ∈ S) :
        c j ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)) ∧
          P.derivative.eval (c j) = 0 := by
      simpa only [c, dif_pos hj] using Classical.choose_spec (hex j hj)
    have hcard : S.card ≤ P.derivative.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn c
      · intro j hj
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hc j hj).2)
      · intro i hi j hj heq
        apply reciprocal_gap_index_unique i j (hS i hi).1 (hS j hj).1 (c i) (hc i hi).1
        rw [heq]
        exact (hc j hj).1
    exact hcard.trans
      ((Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (Polynomial.natDegree_derivative_le P)))

#print axioms occupied_gaps_finset_card_le

/-- All occupied gaps form a finite set, even though the sample sequence
has no finite cutoff. Its cardinality is bounded by the derivative degree. -/
theorem occupied_gaps_finite_card_le
    (P : Polynomial ℝ) (B : ℝ) (hB : 0 < B)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    ∃ S : Finset ℕ,
      (∀ j, j ∈ S ↔ 0 < j ∧
        ∃ t ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)),
          B < |P.eval t|) ∧
      S.card ≤ P.natDegree - 1 := by
  classical
  let A : Set ℕ := {j | 0 < j ∧
    ∃ t ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)), B < |P.eval t|}
  have hfinite : A.Finite := by
    by_contra hinfinite
    obtain ⟨S, hSA, hcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinfinite (P.natDegree - 1 + 1)
    have hbound := occupied_gaps_finset_card_le P B hB hsample S
      (fun j hj => hSA hj)
    omega
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro j
    exact Set.Finite.mem_toFinset hfinite
  · exact occupied_gaps_finset_card_le P B hB hsample _
      (fun j hj => (Set.Finite.mem_toFinset hfinite).mp hj)

#print axioms occupied_gaps_finite_card_le

end RhAstraSynthesis
