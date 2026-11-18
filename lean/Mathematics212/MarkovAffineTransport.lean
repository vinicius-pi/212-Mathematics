import Mathematics212.GevreyMomentFactorial
import Mathlib.Tactic

/-!
# Exact affine transport for iterated polynomial derivatives

For `q(X) = a*X + b` and all `s ≥ 0`:
  `(P ∘ q)^(s) = a^s (P^(s) ∘ q)`
together with the interval mapping `t ↦ 2*k*t - 1` from `[0, 1/k]` into `[-1, 1]`
and conditional supremum-bound transport across that interval.
-/

namespace Mathematics212

/-- Iterated polynomial chain rule for any polynomial with constant derivative. -/
theorem iterate_derivative_comp_const_slope
    (P q : Polynomial ℝ) (a : ℝ)
    (hq : Polynomial.derivative q = Polynomial.C a) (s : ℕ) :
    (Polynomial.derivative^[s]) (P.comp q) =
      Polynomial.C (a^s) * ((Polynomial.derivative^[s]) P).comp q := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rw [Polynomial.derivative_C_mul]
      rw [Polynomial.derivative_comp]
      rw [hq]
      rw [Function.iterate_succ_apply']
      rw [pow_succ]
      rw [← mul_assoc, ← Polynomial.C_mul]

/-- Explicit affine transport of the s-th formal polynomial derivative.
Covers zero slope, s=0, and all polynomial degrees without exceptional cases. -/
theorem iterate_derivative_affine_comp
    (P : Polynomial ℝ) (a b : ℝ) (s : ℕ) :
    (Polynomial.derivative^[s])
        (P.comp (Polynomial.C a * Polynomial.X + Polynomial.C b)) =
      Polynomial.C (a^s) *
        ((Polynomial.derivative^[s]) P).comp
          (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  apply iterate_derivative_comp_const_slope P
    (Polynomial.C a * Polynomial.X + Polynomial.C b) a
  simp [Polynomial.derivative_add]

/-- Evaluated affine derivative identity: the exact factor a^s is visible
and cannot be replaced by an unjustified 2^s or a^{-s}. -/
theorem iterate_derivative_affine_eval
    (P : Polynomial ℝ) (a b x : ℝ) (s : ℕ) :
    ((Polynomial.derivative^[s])
        (P.comp (Polynomial.C a * Polynomial.X + Polynomial.C b))).eval x =
      a^s * ((Polynomial.derivative^[s]) P).eval (a*x+b) := by
  rw [iterate_derivative_affine_comp]
  simp [Polynomial.eval_mul, Polynomial.eval_comp]

/-- The affine map `t ↦ 2*k*t - 1` sends `[0, 1/k]` into `[-1, 1]` for `k > 0`. -/
theorem markov_affine_interval_image
    (k t : ℝ) (hk : 0 < k) (ht : t ∈ Set.Icc (0 : ℝ) (1/k)) :
    2*k*t - 1 ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Set.mem_Icc.mp ht with ⟨h0, h1⟩
  have hcancel : k * (1/k) = 1 := by
    field_simp [ne_of_gt hk]
  have hkt : k*t ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hk)
    simpa only [hcancel] using hmul
  change -1 ≤ 2*k*t - 1 ∧ 2*k*t - 1 ≤ 1
  constructor
  · nlinarith [mul_nonneg (le_of_lt hk) h0]
  · nlinarith

/-- Transports an `s`-th derivative bound for `Q` on `[-1, 1]` to a `(2*k)^s * M`
bound for `Q ∘ (2*k*X - 1)` on `[0, 1/k]`. -/
theorem markov_affine_interval_bound_transfer
    (Q : Polynomial ℝ) (k M : ℝ) (s : ℕ)
    (hk : 0 < k)
    (hbound : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |((Polynomial.derivative^[s]) Q).eval y| ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/k)) :
    |((Polynomial.derivative^[s])
        (Q.comp (Polynomial.C (2*k) * Polynomial.X + Polynomial.C (-1)))).eval t|
      ≤ (2*k)^s * M := by
  have hmem := markov_affine_interval_image k t hk ht
  have hmem' : (2*k)*t + -1 ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa only [sub_eq_add_neg] using hmem
  have hscale : 0 ≤ (2*k)^s := pow_nonneg (by positivity) _
  have hEval := iterate_derivative_affine_eval Q (2*k) (-1) t s
  rw [hEval, abs_mul, abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_left (hbound _ hmem') hscale

end Mathematics212
