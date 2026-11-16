import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic
import RhAstraSynthesis.DivisorMomentBridge

/-!
# Finite modulus-dependent Euler-product transfer

Evaluates the local coprime-removal multiplier `primeMomentRatio p =
(1 - (p / (p + 1)) * p^(-3/4))⁻¹` in `[0, 2)` via `DivisorMomentBridge`,
establishes `2^ω(d) ≤ τ(d)`, and derives the finite divisor-count moment bounds
`finite_euler_ratio_le_divisor_count` and `finite_moment_five_fourths_bound`.
-/

namespace RhAstraSynthesis

noncomputable def primeMomentRatio (p : ℕ) : ℝ :=
  (1 - ((p : ℝ) / ((p : ℝ) + 1)) * (p : ℝ) ^ (-(3 : ℝ) / 4))⁻¹

/-- Both positivity and the upper bound hold also at the exceptional prime two. -/
theorem prime_moment_ratio_bounds (p : ℕ) (hp : p.Prime) :
    0 ≤ primeMomentRatio p ∧ primeMomentRatio p < 2 := by
  by_cases htwo : p = 2
  · subst p
    have ha := two_rpow_neg_three_fourths_lt_three_fifths
    have hden : 0 ≤ 1 - ((2 : ℝ) / 3) * (2 : ℝ) ^ (-(3 : ℝ) / 4) := by linarith
    constructor
    · convert inv_nonneg.mpr hden using 1
      norm_num [primeMomentRatio]
    · convert euler_factor_two_weighted_lt_two using 1
      norm_num [primeMomentRatio]
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hr : (p : ℝ) / ((p : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    have ha := prime_ge_three_rpow_neg_three_fourths_lt_half p hp3
    have hprod : ((p : ℝ) / ((p : ℝ) + 1)) * (p : ℝ) ^ (-(3 : ℝ) / 4) < 1 / 2 := by
      calc
        _ ≤ 1 * (p : ℝ) ^ (-(3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
        _ < 1 / 2 := by simpa using ha
    constructor
    · unfold primeMomentRatio
      exact inv_nonneg.mpr (by linarith)
    · simpa [primeMomentRatio] using
        euler_factor_ge_three_lt_two p hp3 ((p : ℝ) / ((p : ℝ) + 1)) (by positivity) hr

/-- Squarefree-divisor count is bounded by the full divisor count, for every nonzero modulus. -/
theorem two_pow_omega_le_divisor_count (d : ℕ) (hd : d ≠ 0) :
    2 ^ d.primeFactors.card ≤ d.divisors.card := by
  classical
  calc
    2 ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, (2 : ℕ) := by simp
    _ ≤ ∏ p ∈ d.primeFactors, (d.factorization p + 1) := by
      apply Finset.prod_le_prod
      intro p hp
      have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hd
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    _ = d.divisors.card := (Nat.card_divisors hd).symm

/-- Divisor-count bound on the finite Euler product over `d.primeFactors`. -/
theorem finite_euler_ratio_le_divisor_count (d : ℕ) (hd : d ≠ 0) :
    (∏ p ∈ d.primeFactors, primeMomentRatio p) ≤ (d.divisors.card : ℝ) := by
  classical
  have hprod : (∏ p ∈ d.primeFactors, primeMomentRatio p) ≤
      ∏ _p ∈ d.primeFactors, (2 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      exact (prime_moment_ratio_bounds p (Nat.prime_of_mem_primeFactors hp)).1
    · intro p hp
      exact (prime_moment_ratio_bounds p (Nat.prime_of_mem_primeFactors hp)).2.le
  have htau : (2 : ℝ) ^ d.primeFactors.card ≤ (d.divisors.card : ℝ) := by
    exact_mod_cast two_pow_omega_le_divisor_count d hd
  have hprod' : (∏ p ∈ d.primeFactors, primeMomentRatio p) ≤
      (2 : ℝ) ^ d.primeFactors.card := by simpa using hprod
  exact hprod'.trans htau

/-- Scaling bound on a nonnegative base mass by the finite Euler ratio and divisor count. -/
theorem finite_moment_five_fourths_bound (A1 : ℝ) (hA1 : 0 ≤ A1) (d : ℕ) (hd : d ≠ 0) :
    A1 * (∏ p ∈ d.primeFactors, primeMomentRatio p) ≤
      ((5 : ℝ) / 4) * A1 * (d.divisors.card : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (finite_euler_ratio_le_divisor_count d hd) hA1
  have ht : (0 : ℝ) ≤ (d.divisors.card : ℝ) := by positivity
  nlinarith [mul_nonneg hA1 ht]

end RhAstraSynthesis
