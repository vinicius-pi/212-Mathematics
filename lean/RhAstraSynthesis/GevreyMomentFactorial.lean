import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Factorial moment bridge for Gevrey-1 reciprocal-sampling asymptotics

Proves the combinatorial factorial bound `(3s)! / (2s)! = binom(3s, s) * s! ≤ 8^s s!`
for all `s ≥ 0` over both `ℕ` and `ℝ`, converting cubic-degree reciprocal-interval
derivative estimates into Gevrey order-1 scaling.
-/

namespace RhAstraSynthesis

/-- The exact integer factorial inequality, including s=0. -/
theorem factorial_three_mul_le_eight_pow (s : ℕ) :
    (3*s).factorial ≤ 8^s * (2*s).factorial * s.factorial := by
  have hchoose : (3*s).choose s ≤ 8^s := by
    have h := Nat.choose_le_two_pow (3*s) s
    have hpow : 2^(3*s) = 8^s := by
      calc
        2^(3*s) = (2^3)^s := by rw [pow_mul]
        _ = 8^s := by norm_num
    simpa [hpow] using h
  have hfactorial :
      (3*s).choose s * s.factorial * (2*s).factorial =
        (3*s).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (show s ≤ 3*s by omega)
    have hsub : 3*s - s = 2*s := by omega
    simpa only [hsub] using h
  calc
    (3*s).factorial =
        (3*s).choose s * s.factorial * (2*s).factorial := hfactorial.symm
    _ ≤ 8^s * s.factorial * (2*s).factorial := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchoose (Nat.zero_le _)) (Nat.zero_le _)
    _ = 8^s * (2*s).factorial * s.factorial := by ac_rfl

/-- Cast of the factorial bound into real arithmetic for analytic estimates. -/
theorem factorial_three_mul_le_eight_pow_real (s : ℕ) :
    (Nat.factorial (3*s) : ℝ) ≤
      (8:ℝ)^s * (Nat.factorial (2*s) : ℝ) *
        (Nat.factorial s : ℝ) := by
  exact_mod_cast factorial_three_mul_le_eight_pow s

/-- The ratio estimate used after a degree-cubic moment bound. -/
theorem factorial_three_div_two_le_eight_factorial (s : ℕ) :
    (Nat.factorial (3*s) : ℝ) /
        (Nat.factorial (2*s) : ℝ) ≤
      (8:ℝ)^s * (Nat.factorial s : ℝ) := by
  have hpos : (0:ℝ) < (Nat.factorial (2*s) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2*s)
  apply (div_le_iff₀ hpos).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (factorial_three_mul_le_eight_pow_real s)

-- s=0 is equality; the inequality is nontrivial from s=1 onward.
example : (Nat.factorial 0 : ℝ) / (Nat.factorial 0 : ℝ) = 1 := by norm_num
example : (Nat.factorial 3 : ℝ) / (Nat.factorial 2 : ℝ) ≤ 8 := by norm_num
example : (Nat.factorial 6 : ℝ) / (Nat.factorial 4 : ℝ) ≤ 8^2 * 2 := by norm_num

/-- A power is dominated by a rising factorial, in the form needed for the
negative-binomial generating function. -/
theorem power_le_factorial_mul_choose (n j : ℕ) :
    (n + 1) ^ j ≤ j.factorial * (n + j).choose j := by
  simpa only [Nat.ascFactorial_eq_factorial_mul_choose] using
    Nat.pow_succ_le_ascFactorial (n + 1) j

/-- Geometric power moments starting at `m = 1` are summable and have a
factorial bound uniform in the ratio. The shift is intentional: at order zero
the sum is `σ / (1 - σ)`, not `1 / (1 - σ)`.

The majorant is the negative-binomial series, whose exact sum is provided by
Mathlib's `hasSum_choose_mul_geometric_of_norm_lt_one`. -/
theorem geometric_power_moment (j : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ j * σ ^ (n + 1)) ∧
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ j * σ ^ (n + 1)) ≤
        (j.factorial : ℝ) / (1 - σ) ^ (j + 1) := by
  have hnorm : ‖σ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hσ] using hσ1
  have hmajor := (hasSum_choose_mul_geometric_of_norm_lt_one j hnorm).mul_left
    (j.factorial : ℝ)
  have hle (n : ℕ) :
      ((n + 1 : ℕ) : ℝ) ^ j * σ ^ (n + 1) ≤
        (j.factorial : ℝ) * ((n + j).choose j * σ ^ n) := by
    have hp : ((n + 1 : ℕ) : ℝ) ^ j ≤
        (j.factorial : ℝ) * ((n + j).choose j : ℝ) := by
      exact_mod_cast power_le_factorial_mul_choose n j
    have hpow : σ ^ (n + 1) ≤ σ ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hσ n) hσ1.le
    calc
      _ ≤ ((j.factorial : ℝ) * ((n + j).choose j : ℝ)) * σ ^ n :=
        mul_le_mul hp hpow (pow_nonneg hσ _) (by positivity)
      _ = _ := by ring
  have hsum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ j * σ ^ (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hmajor.summable
  refine ⟨hsum, (hsum.tsum_le_tsum hle hmajor.summable).trans_eq ?_⟩
  rw [hmajor.tsum_eq]
  ring

/-- The zero-order positive-index moment, including the endpoint `σ = 0`. -/
theorem geometric_power_moment_zero {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 0 * σ ^ (n + 1)) = σ / (1 - σ) := by
  simpa [pow_succ, div_eq_mul_inv, mul_comm] using
    ((hasSum_geometric_of_lt_one hσ hσ1).mul_right σ).tsum_eq

end RhAstraSynthesis
