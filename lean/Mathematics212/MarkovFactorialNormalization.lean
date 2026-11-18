import Mathematics212.MarkovAlgebraicFactors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# Exact odd-denominator and factorial normalization for Markov's inequality

Algebraic and combinatorial factorial normalizations building on
`MarkovAlgebraicFactors`, proving:
  (2s)! = 2^s s! (1·3·...·(2s-1)) = (2s-1)!! · 2^s s!
and the reciprocal-interval scaling
  (2Lm)^s m^(2s) / ((2s-1)!! s!) = (4L)^s m^(3s) / (2s)!
for all s ≤ m (and unconditionally for the double-factorial scaling), along
with conditional bound-transfer theorems.
-/

namespace Mathematics212

/-- The odd product (2s-1)!!, defined also at s=0. -/
def markovOddDenom (s : ℕ) : ℝ :=
  ∏ j ∈ Finset.range s, (2 * (j : ℝ) + 1)

theorem markovOddDenom_pos (s : ℕ) : 0 < markovOddDenom s := by
  unfold markovOddDenom
  apply Finset.prod_pos
  intro j hj
  positivity

/-- Exact factorial normalization, including the empty product s=0. -/
theorem markov_odd_factorial_identity (s : ℕ) :
    (Nat.factorial (2*s) : ℝ) =
      (2 : ℝ)^s * (Nat.factorial s : ℝ) * markovOddDenom s := by
  induction s with
  | zero =>
      norm_num [markovOddDenom]
  | succ s ih =>
      have hfact :
          (Nat.factorial (2*(s+1)) : ℝ) =
            (2*(s:ℝ)+2) * (2*(s:ℝ)+1) *
              (Nat.factorial (2*s) : ℝ) := by
        have h1 : 2*(s+1) = (2*s+1)+1 := by omega
        have h2 : 2*s+1 = (2*s)+1 := by omega
        rw [h1, Nat.factorial_succ, h2, Nat.factorial_succ]
        push_cast
        ring
      have hsfact :
          (Nat.factorial (s+1) : ℝ) =
            ((s:ℝ)+1) * (Nat.factorial s : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hodd :
          markovOddDenom (s+1) =
            markovOddDenom s * (2*(s:ℝ)+1) := by
        simp [markovOddDenom, Finset.prod_range_succ]
      rw [hfact, hsfact, hodd, pow_succ, ih]
      ring

/-- The exact Markov coefficient is at most its coarse degree-power version.
No classical derivative inequality is assumed or proved by this theorem. -/
theorem markov_normalized_product_le_degree_power
    (m s : ℕ) (hs : s ≤ m) :
    (∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) /
        markovOddDenom s ≤
      (m:ℝ)^(2*s) / markovOddDenom s := by
  have hden : 0 < markovOddDenom s := markovOddDenom_pos s
  apply (div_le_div_iff₀ hden hden).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_right
      (markov_product_le_degree_power m s hs) (le_of_lt hden))

/-- The rescaled algebraic Markov coefficient, for interval length 1/(L*m).
The affine transport of the *derivative inequality* remains unproved. -/
theorem markov_scaled_coefficient_le
    (m s L : ℕ) (hs : s ≤ m) :
    ((∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) /
        markovOddDenom s) * (2 * (L:ℝ) * (m:ℝ))^s ≤
      ((m:ℝ)^(2*s) / markovOddDenom s) *
        (2 * (L:ℝ) * (m:ℝ))^s := by
  exact mul_le_mul_of_nonneg_right
    (markov_normalized_product_le_degree_power m s hs) (by positivity)

/-- Cross-multiplied form of the exact reciprocal-sampling factorial bound.
It avoids division by zero and shows precisely the constant from N=2m²:
  [prod(m²-j²) / D_s] * (4m²)^s / s! ≤ 8^s m^(4s)/(2s)!.
The latter quotient inequality follows because D_s, s! and (2s)! are
strictly positive. No analytic derivative bound is asserted here. -/
theorem markov_sampling_factorial_cross_bound
    (m s : ℕ) (hs : s ≤ m) :
    (∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) *
        (4 * (m:ℝ)^2)^s * (Nat.factorial (2*s) : ℝ) ≤
      (8:ℝ)^s * (m:ℝ)^(4*s) *
        ((Nat.factorial s : ℝ) * markovOddDenom s) := by
  have hbase := markov_product_le_degree_power m s hs
  have hscale : 0 ≤ (4 * (m:ℝ)^2)^s * (Nat.factorial (2*s) : ℝ) := by
    positivity
  have hsq : ((m:ℝ)^2)^s = (m:ℝ)^(2*s) := by
    rw [pow_mul]
  have hpow : (m:ℝ)^(4*s) =
      (m:ℝ)^(2*s) * (m:ℝ)^(2*s) := by
    rw [show 4*s = 2*s + 2*s by omega, pow_add]
  have h8 : (8:ℝ)^s = (4:ℝ)^s * (2:ℝ)^s := by
    rw [show (8:ℝ) = 4*2 by norm_num, mul_pow]
  have hident :
      (m:ℝ)^(2*s) *
        ((4 * (m:ℝ)^2)^s * (Nat.factorial (2*s) : ℝ)) =
      (8:ℝ)^s * (m:ℝ)^(4*s) *
        ((Nat.factorial s : ℝ) * markovOddDenom s) := by
    rw [markov_odd_factorial_identity, mul_pow, hsq, hpow, h8]
    ring
  calc
    (∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) *
        (4 * (m:ℝ)^2)^s * (Nat.factorial (2*s) : ℝ)
      = (∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) *
          ((4 * (m:ℝ)^2)^s * (Nat.factorial (2*s) : ℝ)) := by ring
    _ ≤ (m:ℝ)^(2*s) *
          ((4 * (m:ℝ)^2)^s * (Nat.factorial (2*s) : ℝ)) :=
        mul_le_mul_of_nonneg_right hbase hscale
    _ = _ := hident

/-- On a reciprocal interval of length 1/(L*m), the coarse Markov
numerator contributes m^(2s), while affine rescaling contributes (2Lm)^s.
Their product is (2L)^s m^(3s), not m^(4s). This cubic exponent is
the algebraic prerequisite for the proposed all-radii Gevrey-1 route. -/
theorem markov_remez_cubic_scale (L : ℝ) (m s : ℕ) :
    (m:ℝ)^(2*s) * (2 * L * (m:ℝ))^s =
      (2 * L)^s * (m:ℝ)^(3*s) := by
  have hexp : 3*s = 2*s + s := by omega
  rw [show (2 * L * (m:ℝ))^s =
      (2 * L)^s * (m:ℝ)^s by rw [mul_pow]]
  rw [hexp, pow_add]
  ring

/-- Cross-multiplied factorial bound at the Remez sampling scale.
For nonnegative L and s≤m this is equivalent, using positivity, to
  [prod(m²-j²)/D_s] (2Lm)^s / s! ≤ (4L)^s m^(3s)/(2s)!.
It proves the arithmetic normalization, NOT the analytic Markov inequality. -/
theorem markov_remez_factorial_cross_bound
    (L : ℝ) (hL : 0 ≤ L) (m s : ℕ) (hs : s ≤ m) :
    (∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) *
        (2 * L * (m:ℝ))^s * (Nat.factorial (2*s) : ℝ) ≤
      (4 * L)^s * (m:ℝ)^(3*s) *
        ((Nat.factorial s : ℝ) * markovOddDenom s) := by
  have hbase := markov_product_le_degree_power m s hs
  have hnonneg : 0 ≤ 2 * L * (m:ℝ) := by positivity
  have hscale : 0 ≤ (2 * L * (m:ℝ))^s *
      (Nat.factorial (2*s) : ℝ) :=
    mul_nonneg (pow_nonneg hnonneg s) (by positivity)
  have h4 : (4 * L)^s = (2 * L)^s * (2:ℝ)^s := by
    have heq : (4:ℝ) * L = (2 * L) * 2 := by ring
    rw [heq, mul_pow]
  calc
    (∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) *
        (2 * L * (m:ℝ))^s * (Nat.factorial (2*s) : ℝ)
      = (∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) *
          ((2 * L * (m:ℝ))^s * (Nat.factorial (2*s) : ℝ)) := by ring
    _ ≤ (m:ℝ)^(2*s) *
          ((2 * L * (m:ℝ))^s * (Nat.factorial (2*s) : ℝ)) :=
        mul_le_mul_of_nonneg_right hbase hscale
    _ = (4 * L)^s * (m:ℝ)^(3*s) *
          ((Nat.factorial s : ℝ) * markovOddDenom s) := by
      rw [markov_odd_factorial_identity]
      calc
        _ = ((m:ℝ)^(2*s) * (2 * L * (m:ℝ))^s) *
              ((2:ℝ)^s * ((Nat.factorial s : ℝ) * markovOddDenom s)) := by ring
        _ = ((2 * L)^s * (m:ℝ)^(3*s)) *
              ((2:ℝ)^s * ((Nat.factorial s : ℝ) * markovOddDenom s)) := by
          rw [markov_remez_cubic_scale]
        _ = _ := by rw [h4]; ring

/-- Fully divided factorial normalization at the Remez scale.
The coefficient of the *unproved analytic Markov inequality* would satisfy
  [prod(m²-j²)/D_s] (2Lm)^s / s! ≤ (4L)^s m^(3s)/(2s)!.
This theorem itself is a pure inequality of explicit real numbers. -/
theorem markov_remez_factorial_bound
    (L : ℝ) (hL : 0 ≤ L) (m s : ℕ) (hs : s ≤ m) :
    (((∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) /
        markovOddDenom s) * (2 * L * (m:ℝ))^s) /
        (Nat.factorial s : ℝ) ≤
      ((4 * L)^s * (m:ℝ)^(3*s)) /
        (Nat.factorial (2*s) : ℝ) := by
  have hodd : 0 < markovOddDenom s := markovOddDenom_pos s
  have hfact : (0:ℝ) < (Nat.factorial s : ℝ) := by
    exact_mod_cast Nat.factorial_pos s
  have hfact2 : (0:ℝ) < (Nat.factorial (2*s) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2*s)
  have hcross := markov_remez_factorial_cross_bound L hL m s hs
  calc
    (((∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) /
        markovOddDenom s) * (2 * L * (m:ℝ))^s) /
        (Nat.factorial s : ℝ)
      = ((∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) *
          (2 * L * (m:ℝ))^s) /
            (markovOddDenom s * (Nat.factorial s : ℝ)) := by
        rw [div_mul_eq_mul_div, div_div]
    _ ≤ ((4 * L)^s * (m:ℝ)^(3*s)) /
          (Nat.factorial (2*s) : ℝ) := by
        apply (div_le_div_iff₀ (mul_pos hodd hfact) hfact2).2
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

/-- Explicitly conditional transfer of an exact derivative estimate to the
coarse normalized coefficient. The hypothesis is NOT a proved Markov theorem. -/
theorem markov_pointwise_from_exact_bound
    (P : Polynomial ℝ) (m s L : ℕ) (hs : s ≤ m)
    (B x : ℝ) (hB : 0 ≤ B)
    (hsharp :
      |((Polynomial.derivative^[s]) P).eval x| ≤
        (((∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) /
          markovOddDenom s) * (2 * (L:ℝ) * (m:ℝ))^s) * B) :
    |((Polynomial.derivative^[s]) P).eval x| ≤
      (((m:ℝ)^(2*s) / markovOddDenom s) *
        (2 * (L:ℝ) * (m:ℝ))^s) * B := by
  calc
    _ ≤ (((∏ j ∈ Finset.range s, ((m:ℝ)^2 - (j:ℝ)^2)) /
            markovOddDenom s) * (2 * (L:ℝ) * (m:ℝ))^s) * B := hsharp
    _ ≤ (((m:ℝ)^(2*s) / markovOddDenom s) *
            (2 * (L:ℝ) * (m:ℝ))^s) * B :=
        mul_le_mul_of_nonneg_right (markov_scaled_coefficient_le m s L hs) hB

-- Adversarial boundary checks: s=0, s=1 and s=2.
example : markovOddDenom 0 = 1 := by norm_num [markovOddDenom]
example : markovOddDenom 1 = 1 := by norm_num [markovOddDenom, Finset.prod_range_succ]
example : markovOddDenom 2 = 3 := by norm_num [markovOddDenom, Finset.prod_range_succ]

/-- The odd and even double-factorial product equals `(2*s)!`,
including `s = 0` where `(2*s - 1)` is truncated subtraction in `ℕ`. -/
theorem markov_factorial_double_factorial (s : ℕ) :
    (2*s).factorial =
      (2*s-1).doubleFactorial * (2^s * s.factorial) := by
  cases s with
  | zero =>
      norm_num [Nat.doubleFactorial]
  | succ s =>
      have heq : 2 * (s+1) - 1 + 1 = 2 * (s+1) := by omega
      have h := Nat.factorial_eq_mul_doubleFactorial (2 * (s+1) - 1)
      rw [heq, Nat.doubleFactorial_two_mul] at h
      simpa only [mul_comm] using h

/-- Exact reciprocal-interval constant identity for `I = [0, 1/(L*m)]`:
`(2*L*m)^s * m^(2*s) / ((2*s-1)!! * s!) = (4*L)^s * m^(3*s) / (2*s)!`,
valid for all `s : ℕ`. -/
theorem markov_factorial_scaling (L m : ℝ) (s : ℕ) :
    ((2*L*m)^s * m^(2*s)) /
      (((2*s-1).doubleFactorial : ℝ) * (s.factorial : ℝ)) =
    ((4*L)^s * m^(3*s)) / ((2*s).factorial : ℝ) := by
  have hfactor : ((2*s).factorial : ℝ) =
      ((2*s-1).doubleFactorial : ℝ) * ((2:ℝ)^s * (s.factorial : ℝ)) := by
    exact_mod_cast markov_factorial_double_factorial s
  have hscale : (2*L*m)^s * m^(2*s) * (2:ℝ)^s =
      (4*L)^s * m^(3*s) := by
    calc
      (2*L*m)^s * m^(2*s) * (2:ℝ)^s =
        ((2*L)^s * m^s) * (m^s * m^s) * (2:ℝ)^s := by
          rw [mul_pow, show 2*s = s+s by omega, pow_add]
      _ = ((2*L)^s * (2:ℝ)^s) * (m^s * m^s * m^s) := by ring
      _ = (4*L)^s * m^(3*s) := by
        rw [← mul_pow]
        have hfour : (2*L)*2=4*L := by ring
        rw [hfour, show 3*s=s+s+s by omega, pow_add, pow_add]
  have hpodd : (0:ℝ) < ((2*s-1).doubleFactorial : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2*s-1)
  have hps : (0:ℝ) < (s.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos s
  have hp2s : (0:ℝ) < ((2*s).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2*s)
  apply (div_eq_div_iff (mul_ne_zero hpodd.ne' hps.ne') hp2s.ne').2
  calc
    ((2*L*m)^s * m^(2*s)) * ((2*s).factorial : ℝ) =
      ((2*L*m)^s * m^(2*s) * (2:ℝ)^s) *
        (((2*s-1).doubleFactorial : ℝ) * (s.factorial : ℝ)) := by
          rw [hfactor]
          ring
    _ = ((4*L)^s * m^(3*s)) *
        (((2*s-1).doubleFactorial : ℝ) * (s.factorial : ℝ)) := by rw [hscale]

/-- Converts a double-factorial derivative bound into the `(2*s)!`-normalized form. -/
theorem markov_factored_bound_transfer
    (D M L m : ℝ) (s : ℕ)
    (hclassical :
      D ≤ M * (((2*L*m)^s * m^(2*s)) /
        (((2*s-1).doubleFactorial : ℝ) * (s.factorial : ℝ)))) :
    D ≤ M * (((4*L)^s * m^(3*s)) / ((2*s).factorial : ℝ)) := by
  simpa only [markov_factorial_scaling] using hclassical

end Mathematics212
