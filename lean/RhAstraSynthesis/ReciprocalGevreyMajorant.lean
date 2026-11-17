import RhAstraSynthesis.GevreyMomentFactorial

/-!
# Cubic geometric majorants for reciprocal Gevrey-1

This is the fixed-order analytic summation step, independent of polynomial
representation. Apply it to the weighted absolute Taylor coefficients once the
reciprocal-sample derivative estimate has been normalized to a geometric ratio.
It does not assert a remainder theorem or a fractional-grid extension.
-/

namespace RhAstraSynthesis

/-- A nonnegative sequence dominated by the reciprocal cubic-degree majorant
is summable, with an explicit Gevrey-1 bound. The index `n` represents degree
`m = n + 1`; in particular the order-zero case has no spurious degree-zero term.
The factor `64` is the product of the interval loss `8` and the factorial loss `8`.
-/
theorem cubic_geometric_gevrey_majorant
    (a : ℕ → ℝ) (s : ℕ) {C L σ : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (ha : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, a n ≤
      (C * (8 * L) ^ s / ((2 * s).factorial : ℝ)) *
        (((n + 1 : ℕ) : ℝ) ^ (3 * s) * σ ^ (n + 1))) :
    Summable a ∧ (∑' n, a n) ≤
      C / (1 - σ) * (64 * L / (1 - σ) ^ 3) ^ s * (s.factorial : ℝ) := by
  have hd : 0 < 1 - σ := sub_pos.mpr hσ1
  have hf : (0 : ℝ) < ((2 * s).factorial : ℝ) := by positivity
  let K : ℝ := C * (8 * L) ^ s / ((2 * s).factorial : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨hm, hmoment⟩ := geometric_power_moment (3 * s) hσ hσ1
  have hmajor := hm.mul_left K
  have hsum : Summable a := Summable.of_nonneg_of_le ha hbound hmajor
  refine ⟨hsum, ?_⟩
  calc
    (∑' n, a n) ≤ ∑' n : ℕ,
        K * (((n + 1 : ℕ) : ℝ) ^ (3 * s) * σ ^ (n + 1)) :=
      hsum.tsum_le_tsum hbound hmajor
    _ = K * (∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) ^ (3 * s) * σ ^ (n + 1)) :=
      by rw [tsum_mul_left]
    _ ≤ K * ((Nat.factorial (3 * s) : ℝ) / (1 - σ) ^ (3 * s + 1)) :=
      mul_le_mul_of_nonneg_left hmoment hK
    _ = (C / (1 - σ) * (8 * L / (1 - σ) ^ 3) ^ s) *
        ((Nat.factorial (3 * s) : ℝ) / ((2 * s).factorial : ℝ)) := by
      dsimp [K]
      rw [div_pow, pow_succ, pow_mul]
      ring
    _ ≤ (C / (1 - σ) * (8 * L / (1 - σ) ^ 3) ^ s) *
        ((8 : ℝ) ^ s * (s.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (factorial_three_div_two_le_eight_factorial s)
        (by positivity)
    _ = C / (1 - σ) * (64 * L / (1 - σ) ^ 3) ^ s *
        (s.factorial : ℝ) := by
      have hp : (8 * L / (1 - σ) ^ 3) ^ s * (8 : ℝ) ^ s =
          (64 * L / (1 - σ) ^ 3) ^ s := by
        rw [← mul_pow]
        congr 1
        ring
      calc
        _ = C / (1 - σ) *
            ((8 * L / (1 - σ) ^ 3) ^ s * (8 : ℝ) ^ s) *
            (s.factorial : ℝ) := by ring
        _ = _ := by rw [hp]

end RhAstraSynthesis
