import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Exponential tails in the coprime harmonic estimate

Establishes the exact real-analytic derivative identity `mobius_tail_hasDerivAt`
and explicit polynomial-decay bounds (`polynomial_exp_decay_bound`,
`mobius_tail_polynomial_log_decay`) using Mathlib's `Real.pow_div_factorial_le_exp`
for integrals weighted by negative powers of the logarithm.
-/

namespace RhAstraSynthesis

/-- Exact antiderivative used after the square-root-logarithm substitution. -/
theorem mobius_tail_hasDerivAt (c : ℝ) (hc : 0 < c) (y : ℝ) :
    HasDerivAt
      (fun x ↦ Real.exp (-c * x) *
        (2 * x ^ 3 / c + 6 * x ^ 2 / c ^ 2 + 12 * x / c ^ 3 + 12 / c ^ 4))
      (-2 * y ^ 3 * Real.exp (-c * y)) y := by
  have h3 := (((hasDerivAt_id y).pow 3).const_mul (2 : ℝ)).div_const c
  have h2 := (((hasDerivAt_id y).pow 2).const_mul (6 : ℝ)).div_const (c ^ 2)
  have h1 := ((hasDerivAt_id y).const_mul (12 : ℝ)).div_const (c ^ 3)
  have h0 := hasDerivAt_const y ((12 : ℝ) / c ^ 4)
  have hp : HasDerivAt
      (fun x ↦ 2 * x ^ 3 / c + 6 * x ^ 2 / c ^ 2 + 12 * x / c ^ 3 + 12 / c ^ 4)
      (6 * y ^ 2 / c + 12 * y / c ^ 2 + 12 / c ^ 3) y := by
    convert ((h3.add h2).add h1).add h0 using 1
    · ext x; simp only [Pi.add_apply, Pi.pow_apply, id_eq]; ring
    · simp only [id_eq]; ring
  have he := ((hasDerivAt_id y).const_mul (-c)).exp
  convert he.mul hp using 1
  · ext x; simp only [Pi.mul_apply, id_eq]; ring
  · simp only [id_eq]; field_simp [ne_of_gt hc]; ring

/-- The fifth Taylor term gives a lower bound on `Real.exp t` for `t ≥ 0`. -/
theorem exp_fifth_taylor_lower_bound (t : ℝ) (ht : 0 ≤ t) :
    t ^ 5 / 120 ≤ Real.exp t := by
  convert Real.pow_div_factorial_le_exp (x := t) ht 5 using 1
  norm_num

/-- Explicit decay for any natural polynomial degree and inverse even power. -/
theorem polynomial_exp_decay_bound (c z : ℝ) (hc : 0 < c) (hz : 0 < z)
    (k A : ℕ) :
    z ^ k * Real.exp (-c * z) ≤
      (((k + 2 * A).factorial : ℝ) / c ^ (k + 2 * A)) / z ^ (2 * A) := by
  have ht := Real.pow_div_factorial_le_exp (x := c * z) (by positivity) (k + 2 * A)
  have hexp : Real.exp (c * z) * Real.exp (-c * z) = 1 := by
    rw [← Real.exp_add, show c * z + -c * z = 0 by ring, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_right ht (Real.exp_pos (-c * z)).le
  rw [hexp] at hmul
  have hfac : (0 : ℝ) < ((k + 2 * A).factorial : ℝ) := by positivity
  have hpower : (c * z) ^ (k + 2 * A) * Real.exp (-c * z) ≤
      ((k + 2 * A).factorial : ℝ) := by
    have hdiv : ((c * z) ^ (k + 2 * A) * Real.exp (-c * z)) /
        ((k + 2 * A).factorial : ℝ) ≤ 1 := by
      calc
        _ = ((c * z) ^ (k + 2 * A) / ((k + 2 * A).factorial : ℝ)) *
            Real.exp (-c * z) := by ring
        _ ≤ 1 := hmul
    simpa using (div_le_iff₀ hfac).mp hdiv
  apply (le_div_iff₀ (by positivity : 0 < z ^ (2 * A))).2
  apply (le_div_iff₀ (by positivity : 0 < c ^ (k + 2 * A))).2
  calc
    _ = (c * z) ^ (k + 2 * A) * Real.exp (-c * z) := by
      rw [mul_pow, pow_add]
      ring
    _ ≤ ((k + 2 * A).factorial : ℝ) := hpower

/-- A positive constant depending only on `c,A` controls the cubic tail for all `z ≥ 1`. -/
theorem mobius_tail_polynomial_log_decay (c : ℝ) (hc : 0 < c) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z →
      z ^ 3 * Real.exp (-c * z) ≤ C / z ^ (2 * A) := by
  refine ⟨((3 + 2 * A).factorial : ℝ) / c ^ (3 + 2 * A), by positivity, ?_⟩
  intro z hz
  exact polynomial_exp_decay_bound c z hc (lt_of_lt_of_le zero_lt_one hz) 3 A

end RhAstraSynthesis
