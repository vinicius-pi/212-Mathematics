import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import RhAstraSynthesis.MarkovChebyshevEndpoint
import RhAstraSynthesis.RemezNormalization
import RhAstraSynthesis.ReciprocalSharpnessWitness

/-!
# Chebyshev hyperbolic monotonicity and exponential Remez envelope

Formalizes the analytic Chebyshev–Remez growth chain:
1. `cosh_le_exp_of_nonneg`: for `x ≥ 0`, `Real.cosh x ≤ Real.exp x`.
2. `chebyshev_T_eval_cosh` and `chebyshev_T_cosh_le_exp`:
   `(T_m).eval (Real.cosh x) = Real.cosh (m * x) ≤ Real.exp (m * x)` for `x ≥ 0`.
3. `chebyshev_T_mono_of_one_le`: `T_m` is monotone nondecreasing on `[1, ∞)` via `Real.arcosh`.
4. `self_le_sinh_of_nonneg` and `one_add_sq_div_two_le_cosh`:
   `1 + x^2 / 2 ≤ Real.cosh x` for all `x : ℝ` via `cosh(2y) = 1 + 2 sinh^2(y)`.
5. `chebyshev_T_one_add_two_div_le_exp` and `remez_chebyshev_T_le_exp`:
   for `L > 0` and any good-set measure `e ∈ [1/(Lm + m), 1/(Lm)]`,
   `T_m(2 * (1/(Lm)) / e - 1) ≤ T_m(1 + 2/L) ≤ Real.exp (2 * m / √L)`.
-/

namespace RhAstraSynthesis

open Polynomial

/-- For `x ≥ 0`, `cosh x = (exp x + exp (-x)) / 2 ≤ exp x`. -/
theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have hneg : Real.exp (-x) ≤ Real.exp x :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Evaluation of `T_m` at `cosh x` with natural-number degree cast. -/
theorem chebyshev_T_eval_cosh (m : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (Real.cosh x) = Real.cosh ((m : ℝ) * x) := by
  simpa only [Int.cast_natCast] using Polynomial.Chebyshev.T_real_cosh x (m : ℤ)

/-- For `x ≥ 0`, `T_m(cosh x) = cosh(m * x) ≤ exp(m * x)`. -/
theorem chebyshev_T_cosh_le_exp (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (Real.cosh x) ≤ Real.exp ((m : ℝ) * x) := by
  rw [chebyshev_T_eval_cosh]
  exact cosh_le_exp_of_nonneg (mul_nonneg (Nat.cast_nonneg m) hx)

/-- Monotonicity of `T_m` on `[1, ∞)` via the hyperbolic inverse `Real.arcosh`. -/
theorem chebyshev_T_mono_of_one_le (m : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ≤
      (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y := by
  have hy : 1 ≤ y := hx.trans hxy
  have hx_eq : x = Real.cosh (Real.arcosh x) := (Real.cosh_arcosh hx).symm
  have hy_eq : y = Real.cosh (Real.arcosh y) := (Real.cosh_arcosh hy).symm
  rw [hx_eq, hy_eq, chebyshev_T_eval_cosh, chebyshev_T_eval_cosh, Real.cosh_le_cosh]
  have harx : 0 ≤ Real.arcosh x := Real.arcosh_nonneg hx
  have hary : 0 ≤ Real.arcosh y := Real.arcosh_nonneg hy
  have hmono : Real.arcosh x ≤ Real.arcosh y :=
    (Real.arcosh_le_arcosh (lt_of_lt_of_le zero_lt_one hx) (lt_of_lt_of_le zero_lt_one hy)).2 hxy
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [abs_of_nonneg (mul_nonneg hm harx), abs_of_nonneg (mul_nonneg hm hary)]
  exact mul_le_mul_of_nonneg_left hmono hm

/-- Elementary hyperbolic lower bound `x ≤ sinh x` for `x ≥ 0` from `cosh t ≥ 1`. -/
theorem self_le_sinh_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.sinh x := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun y => Real.sinh y - y) (Real.cosh t - 1) t :=
    fun t => (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
  have hmono : Monotone (fun y => Real.sinh y - y) :=
    monotone_of_hasDerivAt_nonneg hderiv (fun t => sub_nonneg.mpr (Real.one_le_cosh t))
  have h0 : Real.sinh 0 - 0 ≤ Real.sinh x - x := hmono hx
  linarith [Real.sinh_zero]

/-- Quadratic hyperbolic lower bound `1 + x^2 / 2 ≤ cosh x` for all `x : ℝ`
via the half-angle identity `cosh(2y) = 1 + 2 sinh^2(y)`. -/
theorem one_add_sq_div_two_le_cosh (x : ℝ) :
    1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hy : 0 ≤ |x| / 2 := by positivity
  have hsinh : |x| / 2 ≤ Real.sinh (|x| / 2) := self_le_sinh_of_nonneg hy
  have hsq : (|x| / 2) ^ 2 ≤ Real.sinh (|x| / 2) ^ 2 := by nlinarith
  have hdouble : Real.cosh |x| = 1 + 2 * Real.sinh (|x| / 2) ^ 2 := by
    calc
      Real.cosh |x| = Real.cosh (2 * (|x| / 2)) := by ring_nf
      _ = Real.cosh (|x| / 2) ^ 2 + Real.sinh (|x| / 2) ^ 2 := Real.cosh_two_mul (|x| / 2)
      _ = (Real.sinh (|x| / 2) ^ 2 + 1) + Real.sinh (|x| / 2) ^ 2 := by rw [Real.cosh_sq (|x| / 2)]
      _ = 1 + 2 * Real.sinh (|x| / 2) ^ 2 := by ring
  calc
    1 + x ^ 2 / 2 = 1 + |x| ^ 2 / 2 := by rw [sq_abs]
    _ = 1 + 2 * (|x| / 2) ^ 2 := by ring
    _ ≤ 1 + 2 * Real.sinh (|x| / 2) ^ 2 := by linarith
    _ = Real.cosh |x| := hdouble.symm
    _ = Real.cosh x := Real.cosh_abs x

/-- Specialization at `x = 2 / √L`: `1 + 2 / L ≤ cosh(2 / √L)` for `L > 0`. -/
theorem one_add_two_div_le_cosh_two_div_sqrt {L : ℝ} (hL : 0 < L) :
    1 + 2 / L ≤ Real.cosh (2 / Real.sqrt L) := by
  have h := one_add_sq_div_two_le_cosh (2 / Real.sqrt L)
  have hsq : (2 / Real.sqrt L) ^ 2 / 2 = 2 / L := by
    rw [div_pow, Real.sq_sqrt hL.le]
    ring
  linarith

/-- Exponential Chebyshev envelope: `T_m(1 + 2 / L) ≤ exp(2 * m / √L)` for `L > 0`. -/
theorem chebyshev_T_one_add_two_div_le_exp (m : ℕ) {L : ℝ} (hL : 0 < L) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (1 + 2 / L) ≤
      Real.exp (2 * (m : ℝ) / Real.sqrt L) := by
  have h1 : 1 ≤ 1 + 2 / L := by
    have : (0 : ℝ) < 2 / L := by positivity
    linarith
  have hle := one_add_two_div_le_cosh_two_div_sqrt hL
  have hmono := chebyshev_T_mono_of_one_le m h1 hle
  have hexp := chebyshev_T_cosh_le_exp m (show (0 : ℝ) ≤ 2 / Real.sqrt L by positivity)
  have hscale : (m : ℝ) * (2 / Real.sqrt L) = 2 * (m : ℝ) / Real.sqrt L := by ring
  calc
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (1 + 2 / L)
        ≤ (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (Real.cosh (2 / Real.sqrt L)) := hmono
    _ ≤ Real.exp ((m : ℝ) * (2 / Real.sqrt L)) := hexp
    _ = Real.exp (2 * (m : ℝ) / Real.sqrt L) := by rw [hscale]

/-- Full Remez–Chebyshev exponential upper bound: for `1 / (L*m + m) ≤ e ≤ 1 / (L*m)`,
the Chebyshev factor at the Remez argument `2 * (1 / (L*m)) / e - 1` is at most `exp(2 * m / √L)`. -/
theorem remez_chebyshev_T_le_exp (m : ℕ) {L e : ℝ}
    (hL : 0 < L) (hm : 0 < (m : ℝ))
    (hmeas_low : 1 / (L * (m : ℝ) + (m : ℝ)) ≤ e)
    (hmeas_high : e ≤ 1 / (L * (m : ℝ))) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (2 * (1 / (L * (m : ℝ))) / e - 1) ≤
      Real.exp (2 * (m : ℝ) / Real.sqrt L) := by
  have hp : 0 < L * (m : ℝ) := mul_pos hL hm
  have hsum : 0 < L * (m : ℝ) + (m : ℝ) := add_pos hp hm
  have he : 0 < e := lt_of_lt_of_le (one_div_pos.mpr hsum) hmeas_low
  have h1 : 1 ≤ 2 * (1 / (L * (m : ℝ))) / e - 1 := by
    have hmul : 2 * e ≤ 2 * (1 / (L * (m : ℝ))) := by linarith
    have hdiv : 2 ≤ 2 * (1 / (L * (m : ℝ))) / e := (le_div_iff₀ he).2 hmul
    linarith
  have harg := remez_argument_of_measure L (m : ℝ) e hL hm hmeas_low
  exact (chebyshev_T_mono_of_one_le m h1 harg).trans (chebyshev_T_one_add_two_div_le_exp m hL)

end RhAstraSynthesis
