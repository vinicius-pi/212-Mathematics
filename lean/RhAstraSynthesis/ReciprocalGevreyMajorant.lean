import RhAstraSynthesis.GevreyMomentFactorial
import RhAstraSynthesis.RemezInequality

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
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
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

/-- Normalize the exponential degree loss before summing over a family. -/
theorem reciprocal_exponential_weight (m : ℕ) (r R L : ℝ) :
    Real.exp (2 * (m : ℝ) / Real.sqrt L) * (1 / R) ^ m * r ^ m =
      ((r / R) * Real.exp (2 / Real.sqrt L)) ^ m := by
  have he : Real.exp (2 * (m : ℝ) / Real.sqrt L) =
      Real.exp (2 / Real.sqrt L) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, ← mul_pow, ← mul_pow]
  congr 1
  ring

/-- The sampled polynomial estimate, including derivative orders above the degree.
The radius may be zero; no hypothesis on the degree-zero polynomial is needed. -/
theorem polynomial_reciprocal_family_pointwise
    (P : ℕ → Polynomial ℝ) (m s L : ℕ) {C R r : ℝ}
    (hC : 0 < C) (hR : 0 < R) (hr : 0 ≤ r) (hL : 0 < L)
    (hm : 0 < m) (hdegree : (P m).natDegree ≤ m)
    (hsample : ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m) :
    |((Polynomial.derivative^[s]) (P m)).eval 0| / (s.factorial : ℝ) * r ^ m ≤
      (C * (8 * (L : ℝ)) ^ s / ((2 * s).factorial : ℝ)) *
        ((m : ℝ) ^ (3 * s) * ((r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ m) := by
  by_cases hs : s ≤ m
  · have hb := polynomial_reciprocal_sample_factorial_bound
      (P m) (C * (1 / R) ^ m) L m s (by positivity) hL hm hs hdegree hsample
      (x := 0) ⟨le_rfl, by positivity⟩
    have hw := mul_le_mul_of_nonneg_right hb (pow_nonneg hr m)
    refine hw.trans_eq ?_
    calc
      _ = (C * (8 * (L : ℝ)) ^ s / ((2 * s).factorial : ℝ)) *
          ((m : ℝ) ^ (3 * s) *
            (Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * (1 / R) ^ m * r ^ m)) := by ring
      _ = _ := by rw [reciprocal_exponential_weight]
  · have hz : (Polynomial.derivative^[s]) (P m) = 0 :=
      Polynomial.iterate_derivative_eq_zero (hdegree.trans_lt (Nat.lt_of_not_ge hs))
    rw [hz]
    simp only [Polynomial.eval_zero, abs_zero, zero_div, zero_mul]
    positivity

/-- Reciprocal samples for a degree-controlled polynomial family imply absolute
summability of every weighted Taylor order and an explicit Gevrey-1 bound.
This is a coefficient-series result, not a remainder or fractional-grid theorem. -/
theorem polynomial_reciprocal_family_gevrey
    (P : ℕ → Polynomial ℝ) (s L : ℕ) {C R r : ℝ}
    (hC : 0 < C) (hR : 0 < R) (hr : 0 ≤ r) (hL : 0 < L)
    (hdegree : ∀ m, 0 < m → (P m).natDegree ≤ m)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m)
    (hσ : (r / R) * Real.exp (2 / Real.sqrt (L : ℝ)) < 1) :
    Summable (fun n : ℕ =>
      |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
        (s.factorial : ℝ) * r ^ (n + 1)) ∧
      (∑' n : ℕ, |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
        (s.factorial : ℝ) * r ^ (n + 1)) ≤
      C / (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) *
        (64 * (L : ℝ) /
          (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ 3) ^ s *
        (s.factorial : ℝ) := by
  apply cubic_geometric_gevrey_majorant _ s hC.le (Nat.cast_nonneg L)
    (mul_nonneg (div_nonneg hr hR.le) (Real.exp_pos _).le) hσ
  · intro n
    positivity
  · intro n
    exact polynomial_reciprocal_family_pointwise P (n + 1) s L hC hR hr hL
      (Nat.succ_pos n) (hdegree _ (Nat.succ_pos n)) (hsample _ (Nat.succ_pos n))

end RhAstraSynthesis
