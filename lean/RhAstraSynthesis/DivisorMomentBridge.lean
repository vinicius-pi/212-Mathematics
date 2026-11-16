import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Arithmetic and Euler-factor inequalities for modulus-uniform fractional moments

Formalizes the elementary inequalities used in the modulus-uniform
`s = 3/4` fractional-moment divisor bounds:
1. `τ(p^e)^2 ≤ d_4(p^e)` at every prime power exponent `e : ℕ`:
   `6 (e + 1)^2 ≤ (e + 1)(e + 2)(e + 3)` and `(e + 1)^2 ≤ Nat.choose (e + 3) 3`,
   giving the convergent global series `∑ τ(d)^2 / d^(7/4) ≤ ζ(7/4)^4`.
2. Sharp local Euler-factor bounds at exponent `s = 3/4`:
   - `2^(-3/4) < 3/5`, giving `(1 - 2^(-3/4))⁻¹ < 5/2`,
   - With `r_2 = 2/3`, `(1 - (2/3) * 2^(-3/4))⁻¹ < 2`,
   - For all `p ≥ 3`, `p^(-3/4) < 1/2` and `(1 - r * p^(-3/4))⁻¹ < 2` (`0 ≤ r ≤ 1`),
   whence `A(d) ≤ A(1) * 2^(ω(d)) ≤ A(1) * τ(d)` uniformly in `d`.
-/

namespace RhAstraSynthesis

/-- Exponentwise prime-power bound `(e+1)^2 ≤ (e+1)(e+2)(e+3)/6` (equality at `e = 0, 1`). -/
theorem tau_sq_le_d4_exponent_mul (e : ℕ) :
    6 * (e + 1) ^ 2 ≤ (e + 1) * (e + 2) * (e + 3) := by
  rcases e with _ | e
  · norm_num
  · rcases e with _ | e
    · norm_num
    · have hquad : 6 * (e + 3) ≤ (e + 4) * (e + 5) := by nlinarith
      calc
        6 * (e + 1 + 1 + 1) ^ 2 = (e + 3) * (6 * (e + 3)) := by ring
        _ ≤ (e + 3) * ((e + 4) * (e + 5)) := Nat.mul_le_mul_left _ hquad
        _ = (e + 1 + 1 + 1) * (e + 1 + 1 + 2) * (e + 1 + 1 + 3) := by ring

/-- Binomial form `(e + 1)^2 ≤ Nat.choose (e + 3) 3` proving `τ(n)^2 ≤ d_4(n)`. -/
theorem tau_sq_le_choose_three (e : ℕ) :
    (e + 1) ^ 2 ≤ Nat.choose (e + 3) 3 := by
  have hmul : (e + 3).descFactorial 3 = 6 * Nat.choose (e + 3) 3 := by
    simpa [show Nat.factorial 3 = 6 by decide] using
      (Nat.descFactorial_eq_factorial_mul_choose (e + 3) 3)
  have hdesc : (e + 3).descFactorial 3 = (e + 1) * (e + 2) * (e + 3) := by
    simp [Nat.descFactorial_succ]
    ring
  have hle : 6 * (e + 1) ^ 2 ≤ 6 * Nat.choose (e + 3) 3 := by
    rw [← hmul, hdesc]
    exact tau_sq_le_d4_exponent_mul e
  exact Nat.le_of_mul_le_mul_left hle (by decide : 0 < 6)

/-- Numerical fractional-power bound `2^(-3/4) < 3/5` (`(3/5)^4 = 81/625 > 1/8 = 2^(-3)`). -/
theorem two_rpow_neg_three_fourths_lt_three_fifths :
    (2 : ℝ) ^ (-(3 : ℝ) / 4) < (3 : ℝ) / 5 := by
  have hpos : 0 < (2 : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
  have hpow : ((2 : ℝ) ^ (-(3 : ℝ) / 4)) ^ 4 < ((3 : ℝ) / 5) ^ 4 := by
    have h4 : ((2 : ℝ) ^ (-(3 : ℝ) / 4)) ^ 4 = (2 : ℝ) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(3 : ℝ) / 4)) 4,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h4]
    norm_num [Real.rpow_neg]
  exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) hpow

/-- Local `p = 2` unrestricted Euler factor: `(1 - 2^(-3/4))⁻¹ < 5/2`. -/
theorem euler_factor_two_unrestricted_lt :
    (1 - (2 : ℝ) ^ (-(3 : ℝ) / 4))⁻¹ < (5 : ℝ) / 2 := by
  have h2 := two_rpow_neg_three_fourths_lt_three_fifths
  have hden : (2 : ℝ) / 5 < 1 - (2 : ℝ) ^ (-(3 : ℝ) / 4) := by linarith
  have hinv := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 2 / 5) hden
  simpa [inv_div] using hinv

/-- Sharp `p = 2` weighted Euler factor with `r_2 = 2/3`: `(1 - (2/3) * 2^(-3/4))⁻¹ < 2`. -/
theorem euler_factor_two_weighted_lt_two :
    (1 - ((2 : ℝ) / 3) * (2 : ℝ) ^ (-(3 : ℝ) / 4))⁻¹ < 2 := by
  have h2 := two_rpow_neg_three_fourths_lt_three_fifths
  have hden : (1 : ℝ) / 2 < 1 - ((2 : ℝ) / 3) * (2 : ℝ) ^ (-(3 : ℝ) / 4) := by linarith
  have hinv := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
  simpa using hinv

/-- For every integer `p ≥ 3`, `p^(-3/4) < 1/2` (`(1/2)^4 = 1/16 > 1/27 ≥ p^(-3)`). -/
theorem prime_ge_three_rpow_neg_three_fourths_lt_half (p : ℕ) (hp : 3 ≤ p) :
    (p : ℝ) ^ (-(3 : ℝ) / 4) < (1 : ℝ) / 2 := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hpow : ((p : ℝ) ^ (-(3 : ℝ) / 4)) ^ 4 < ((1 : ℝ) / 2) ^ 4 := by
    have h4 : ((p : ℝ) ^ (-(3 : ℝ) / 4)) ^ 4 = (p : ℝ) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-(3 : ℝ) / 4)) 4,
        ← Real.rpow_mul hp_pos.le]
      norm_num
    rw [h4, show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hp_pos.le,
      Real.rpow_natCast]
    have hcube : (27 : ℝ) ≤ (p : ℝ) ^ 3 := by
      have h27 : (27 : ℝ) = (3 : ℝ) ^ 3 := by norm_num
      rw [h27]
      exact pow_le_pow_left₀ (by norm_num) hpR 3
    have hinv : ((p : ℝ) ^ 3)⁻¹ ≤ (27 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hcube
    linarith [show ((1 : ℝ) / 2) ^ 4 = 1 / 16 by norm_num,
      show (27 : ℝ)⁻¹ = 1 / 27 by norm_num]
  exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) hpow

/-- For all `p ≥ 3` and `0 ≤ r ≤ 1`, the local Euler factor satisfies `(1 - r * p^(-3/4))⁻¹ < 2`. -/
theorem euler_factor_ge_three_lt_two (p : ℕ) (hp : 3 ≤ p) (r : ℝ)
    (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r * (p : ℝ) ^ (-(3 : ℝ) / 4))⁻¹ < 2 := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_nonneg : 0 ≤ (p : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
  have hlt := prime_ge_three_rpow_neg_three_fourths_lt_half p hp
  have hprod : r * (p : ℝ) ^ (-(3 : ℝ) / 4) < (1 : ℝ) / 2 := by
    calc
      r * (p : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 * (p : ℝ) ^ (-(3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hr1 hp_nonneg
      _ < (1 : ℝ) / 2 := by linarith
  have hden : (1 : ℝ) / 2 < 1 - r * (p : ℝ) ^ (-(3 : ℝ) / 4) := by linarith
  have hinv := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
  simpa using hinv

#print axioms tau_sq_le_d4_exponent_mul
#print axioms tau_sq_le_choose_three
#print axioms two_rpow_neg_three_fourths_lt_three_fifths
#print axioms euler_factor_two_unrestricted_lt
#print axioms euler_factor_two_weighted_lt_two
#print axioms prime_ge_three_rpow_neg_three_fourths_lt_half
#print axioms euler_factor_ge_three_lt_two

end RhAstraSynthesis
