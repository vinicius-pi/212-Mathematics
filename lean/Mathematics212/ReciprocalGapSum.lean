import Mathematics212.ReciprocalGapOrder
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace Mathematics212

/-- Length of the j-th reciprocal gap; used only at positive indices. -/
noncomputable def reciprocalGapLength (j : ℕ) : ℝ :=
  1 / (j : ℝ) - 1 / (↑(j+1) : ℝ)

/-- Any finite set of indices above k has no more total gap length
than the first equally many indices above k. -/
theorem reciprocal_gaps_sum_le_initial (S : Finset ℕ) :
    ∀ k : ℕ, 0 < k → (∀ j ∈ S, k ≤ j) →
      ∑ j ∈ S, reciprocalGapLength j ≤
        ∑ i ∈ Finset.range S.card, reciprocalGapLength (k+i) := by
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert a S hmin ih =>
    intro k hk hbound
    have ha : k ≤ a := hbound a (by simp)
    have hnot : a ∉ S := by
      intro h
      exact (lt_irrefl a) (hmin a h)
    have htail : ∀ j ∈ S, k+1 ≤ j := by
      intro j hj
      have h := hmin j hj
      omega
    calc
      ∑ j ∈ insert a S, reciprocalGapLength j =
          reciprocalGapLength a + ∑ j ∈ S, reciprocalGapLength j :=
        Finset.sum_insert hnot
      _ ≤ reciprocalGapLength k +
          ∑ i ∈ Finset.range S.card, reciprocalGapLength (k+1+i) :=
        add_le_add (reciprocal_gap_length_antitone k a hk ha)
          (ih (k+1) (by omega) htail)
      _ = ∑ i ∈ Finset.range (insert a S).card,
          reciprocalGapLength (k+i) := by
        rw [Finset.card_insert_of_notMem hnot, Finset.sum_range_succ']
        simp only [Nat.add_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        omega

/-- The same majorization with an externally supplied upper bound on
the number of occupied gaps. This is a finite-sum lemma, not a measure theorem. -/
theorem reciprocal_gaps_sum_le_first_m
    (S : Finset ℕ) (k m : ℕ) (hk : 0 < k)
    (hbound : ∀ j ∈ S, k ≤ j) (hcard : S.card ≤ m) :
    ∑ j ∈ S, reciprocalGapLength j ≤
      ∑ i ∈ Finset.range m, reciprocalGapLength (k+i) := by
  apply (reciprocal_gaps_sum_le_initial S k hk hbound).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcard)
  intro i hi hnot
  dsimp [reciprocalGapLength]
  apply sub_nonneg.mpr
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast (Nat.le_succ (k+i))

end Mathematics212
