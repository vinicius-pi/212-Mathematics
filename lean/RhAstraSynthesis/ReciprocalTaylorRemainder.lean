import RhAstraSynthesis.RemezInequality
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Finite reciprocal Taylor remainders

Lagrange remainders on reciprocal intervals with factorial derivative control.
-/

noncomputable section
namespace RhAstraSynthesis
open Set Polynomial

private lemma reciprocal_polynomial_contDiff (P : Polynomial ℝ) (s : WithTop ℕ∞) :
    ContDiff ℝ s (fun x : ℝ => P.eval x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa using hP.add hQ
  | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow n)

/-- Analytic and algebraic iterated derivatives agree. -/
lemma reciprocal_iteratedDeriv_eval (P : Polynomial ℝ) (s : ℕ) :
    iteratedDeriv s (fun x : ℝ => P.eval x) =
      fun x => ((Polynomial.derivative^[s]) P).eval x := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    simp only [Polynomial.deriv, Function.iterate_succ_apply']

/-- The normalized derivatives used by the profiles really are coefficients. -/
lemma reciprocal_normalized_derivative_coeff (P : Polynomial ℝ) (s : ℕ) :
    ((Polynomial.derivative^[s]) P).eval 0 / (s.factorial : ℝ) = P.coeff s := by
  have hz : ((Polynomial.derivative^[s]) P).eval 0 =
      ((Polynomial.derivative^[s]) P).coeff 0 := by
    have hzero (Q : Polynomial ℝ) : Q.eval 0 = Q.coeff 0 := by
      induction Q using Polynomial.induction_on' with
      | add Q T hQ hT => simp [hQ, hT]
      | monomial n a =>
        by_cases hn : n = 0
        · simp [hn]
        · simp [hn, Ne.symm hn]
    exact hzero _
  rw [hz, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by positivity : (s.factorial : ℝ) ≠ 0)

private lemma within_derivative_polynomial (P : Polynomial ℝ) (s : ℕ)
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    iteratedDerivWithin s (fun t : ℝ => P.eval t) (Icc a b) x =
      ((Polynomial.derivative^[s]) P).eval x := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
    (reciprocal_polynomial_contDiff P s).contDiffAt hx,
    reciprocal_iteratedDeriv_eval]

/-- Exact coefficient form of the actual Taylor polynomial, including order zero. -/
lemma reciprocal_taylorWithinEval (P : Polynomial ℝ) (q : ℕ)
    {b : ℝ} (hb : 0 < b) (x : ℝ) :
    taylorWithinEval (fun t : ℝ => P.eval t) q (Icc 0 b) 0 x =
      ∑ s ∈ Finset.range (q + 1), P.coeff s * x ^ s := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro s hs
  rw [within_derivative_polynomial P s hb ⟨le_rfl, hb.le⟩]
  have hc := reciprocal_normalized_derivative_coeff P s
  simp only [sub_zero, smul_eq_mul]
  rw [← hc]
  ring

/-- Lagrange's theorem with `p` terms, expressed in polynomial coefficients.
The witness is in the open segment; no remainder estimate is assumed. -/
theorem reciprocal_polynomial_lagrange (P : Polynomial ℝ) (p : ℕ)
    (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    ∃ y ∈ Ioo (0 : ℝ) x,
      P.eval x - (∑ s ∈ Finset.range p, P.coeff s * x ^ s) =
        (x ^ p / (p.factorial : ℝ)) *
          ((Polynomial.derivative^[p]) P).eval y := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hfull : ContDiffOn ℝ (q + 1) (fun t : ℝ => P.eval t) (Icc 0 x) :=
    (reciprocal_polynomial_contDiff P (q + 1)).contDiffOn
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (ne_of_lt hx) (by simpa only [uIcc_of_le hx.le] using hfull)
  rw [uIoo_of_lt hx] at hy
  rw [uIcc_of_le hx.le, reciprocal_taylorWithinEval P q hx,
    reciprocal_iteratedDeriv_eval, sub_zero] at heq
  refine ⟨y, hy, ?_⟩
  calc
    _ = _ := heq
    _ = _ := by simp only [Nat.succ_eq_add_one]; ring

/-- Above the degree the finite Taylor remainder vanishes identically. -/
theorem reciprocal_taylor_remainder_zero (P : Polynomial ℝ) (m p : ℕ)
    (hdegree : P.natDegree ≤ m) (hmp : m < p) {x : ℝ} (hx : 0 < x) :
    P.eval x - (∑ s ∈ Finset.range p, P.coeff s * x ^ s) = 0 := by
  obtain ⟨y, hy, heq⟩ := reciprocal_polynomial_lagrange P p (by omega) hx
  rw [Polynomial.iterate_derivative_eq_zero (hdegree.trans_lt hmp)] at heq
  simpa using heq

/-- The small-degree reciprocal Gevrey-1 remainder, retaining `(2p)!`.
The sample assumption is on every positive reciprocal, not the target alone. -/
theorem polynomial_reciprocal_taylor_remainder_bound
    (P : Polynomial ℝ) (B : ℝ) (L m n p : ℕ)
    (hB : 0 < B) (hL : 0 < L) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (hsmall : L * m ≤ n) (hdegree : P.natDegree ≤ m)
    (hsample : ∀ k : ℕ, 0 < k → |P.eval (1 / (k : ℝ))| ≤ B) :
    |P.eval (1 / (n : ℝ)) -
      (∑ s ∈ Finset.range p, P.coeff s * (1 / (n : ℝ)) ^ s)| ≤
      Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * B *
        (8 * (L : ℝ)) ^ p * (m : ℝ) ^ (3 * p) /
          (((2 * p).factorial : ℝ) * (n : ℝ) ^ p) := by
  have hx : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  by_cases hpm : p ≤ m
  · obtain ⟨y, hy, heq⟩ := reciprocal_polynomial_lagrange P p hp hx
    have hcast : (L : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsmall
    have hsegment : y ∈ Icc (0 : ℝ) (1 / ((L : ℝ) * (m : ℝ))) := by
      refine ⟨hy.1.le, hy.2.le.trans ?_⟩
      exact one_div_le_one_div_of_le (by positivity) hcast
    have hd := polynomial_reciprocal_sample_factorial_bound
      P B L m p hB hL hm hpm hdegree hsample hsegment
    rw [heq, abs_mul, abs_div, abs_of_pos (pow_pos hx p),
      abs_of_pos (by positivity : (0 : ℝ) < (p.factorial : ℝ))]
    calc
      (1 / (n : ℝ)) ^ p / (p.factorial : ℝ) *
          |((Polynomial.derivative^[p]) P).eval y| =
          (|((Polynomial.derivative^[p]) P).eval y| / (p.factorial : ℝ)) *
            (1 / (n : ℝ)) ^ p := by ring
      _ ≤ ((Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * B) *
            (((8 * (L : ℝ)) ^ p * (m : ℝ) ^ (3 * p)) /
              ((2 * p).factorial : ℝ))) * (1 / (n : ℝ)) ^ p :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ = _ := by rw [div_pow, one_pow]; ring
  · rw [reciprocal_taylor_remainder_zero P m p hdegree (by omega) hx, abs_zero]
    positivity

/-- A genuine nonzero remainder at the boundary `n = Lm`: `X²`, `p = 2`.
This is not a witness whose remainder vanishes for degree reasons. -/
theorem reciprocal_taylor_nonzero_witness :
    (Polynomial.X ^ 2 : Polynomial ℝ).eval (1 / 4) -
      (∑ s ∈ Finset.range 2,
        (Polynomial.X ^ 2 : Polynomial ℝ).coeff s * (1 / 4 : ℝ) ^ s) = 1 / 16 := by
  norm_num [Finset.sum_range_succ, Polynomial.coeff_X_pow]

end RhAstraSynthesis
