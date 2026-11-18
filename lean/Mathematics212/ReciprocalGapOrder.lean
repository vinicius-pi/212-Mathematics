import Mathlib.Tactic

/-!
# Reciprocal gap lengths decrease

Proves antitone monotonicity of consecutive reciprocal gap lengths `1/n - 1/(n+1)`.
-/

namespace Mathematics212

/-- For positive integers k ≤ j, the j-th reciprocal gap is no longer
than the k-th gap. -/
theorem reciprocal_gap_length_antitone
    (k j : ℕ) (hk : 0 < k) (hkj : k ≤ j) :
    (1 : ℝ) / (j : ℝ) - (1 : ℝ) / (↑(j+1) : ℝ) ≤
      (1 : ℝ) / (k : ℝ) - (1 : ℝ) / (↑(k+1) : ℝ) := by
  have hj : 0 < j := lt_of_lt_of_le hk hkj
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hkjR : (k : ℝ) ≤ j := by exact_mod_cast hkj
  have hprod :
      (k : ℝ) * ((k : ℝ) + 1) ≤ (j : ℝ) * ((j : ℝ) + 1) := by
    have hh : 0 ≤ ((j : ℝ) - k) * ((j : ℝ) + k + 1) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hformula (n : ℕ) (hn : 0 < n) :
      (1 : ℝ) / (n : ℝ) - (1 : ℝ) / (↑(n+1) : ℝ) =
        1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hn10 : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp [hn0, hn10]
    ring
  rw [hformula j hj, hformula k hk]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

end Mathematics212
