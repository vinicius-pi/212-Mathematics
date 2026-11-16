import Mathlib.Tactic

/-!
# Reciprocal-sampling finite gap telescoping

This proves the exact *finite telescoping identity* for reciprocal-node gaps:

`∑_{j=0}^{m-1} (1 / (k + j) - 1 / (k + j + 1)) = 1 / k - 1 / (k + m)`.

It is strictly the algebraic telescoping step preceding good-set measure
estimation and Markov–Chebyshev derivative bounds.
-/

namespace RhAstraSynthesis

/--
For `k > 0`, the total lengths of the first `m` consecutive
reciprocal-node gaps beginning at `1/k` telescope exactly.
-/
theorem reciprocal_gap_telescope (k m : ℕ) (hk : 0 < k) :
    (∑ j ∈ Finset.range m,
      ((1 : ℝ) / (↑(k + j) : ℝ) -
        (1 : ℝ) / (↑(k + j + 1) : ℝ))) =
      (1 : ℝ) / (↑k : ℝ) -
        (1 : ℝ) / (↑(k + m) : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring

/-- The equivalent remaining-length identity in source equation (4). -/
theorem reciprocal_gap_remaining (k m : ℕ) (hk : 0 < k) :
    (1 : ℝ) / (↑k : ℝ) -
      (∑ j ∈ Finset.range m,
        ((1 : ℝ) / (↑(k + j) : ℝ) -
          (1 : ℝ) / (↑(k + j + 1) : ℝ))) =
      (1 : ℝ) / (↑(k + m) : ℝ) := by
  rw [reciprocal_gap_telescope k m hk]
  ring

#print axioms RhAstraSynthesis.reciprocal_gap_telescope
#print axioms RhAstraSynthesis.reciprocal_gap_remaining

end RhAstraSynthesis
