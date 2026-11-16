import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Algebraic factors and degree endpoints of the higher-order Markov step

Formalizes the polynomial degree and Markov coefficient envelopes:
* For `0 ≤ s ≤ m`, the Markov product `∏_{j=0}^{s-1} (m² - j²)` is bounded by `m^(2s)`.
* For `s > m ≥ deg P`, the `s`-th derivative vanishes identically, and at `s = m`
  the top derivative is constant.
-/

namespace RhAstraSynthesis

/-- The exact Markov product is bounded by the coarse power used in (6).
The empty-product case s=0 is included. -/
theorem markov_product_le_degree_power (m s : ℕ) (hs : s ≤ m) :
    (∏ j ∈ Finset.range s,
      ((m : ℝ)^2 - (j : ℝ)^2)) ≤ (m : ℝ)^(2*s) := by
  have hfactor (j : ℕ) (hj : j ∈ Finset.range s) :
      0 ≤ (m : ℝ)^2 - (j : ℝ)^2 := by
    have hjs : j < s := Finset.mem_range.mp hj
    have hjm : (j : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (le_trans (Nat.le_of_lt hjs) hs)
    have hprod : 0 ≤ ((m : ℝ) - (j : ℝ)) * ((m : ℝ) + (j : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hjm) (by positivity)
    nlinarith
  calc
    (∏ j ∈ Finset.range s, ((m : ℝ)^2 - (j : ℝ)^2))
      ≤ ∏ _j ∈ Finset.range s, (m : ℝ)^2 := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact hfactor j hj
        · intro j hj
          nlinarith [sq_nonneg (j : ℝ)]
    _ = ((m : ℝ)^2)^s := by simp
    _ = (m : ℝ)^(2*s) := by rw [pow_mul]

/-- The s>m endpoint of equation (6), without a derivative norm premise. -/
theorem markov_derivative_zero_above_degree
    (P : Polynomial ℝ) (m s : ℕ)
    (hdegree : P.natDegree ≤ m) (hsm : m < s) :
    (Polynomial.derivative^[s]) P = 0 := by
  exact Polynomial.iterate_derivative_eq_zero
    (lt_of_le_of_lt hdegree hsm)

/-- At the highest allowed derivative order, the polynomial is constant.
This covers s=m even when the original degree is strictly below m. -/
theorem markov_top_derivative_constant
    (P : Polynomial ℝ) (m : ℕ) (hdegree : P.natDegree ≤ m) :
    (Polynomial.derivative^[m]) P =
      Polynomial.C (((Polynomial.derivative^[m]) P).coeff 0) := by
  have hnat :
      ((Polynomial.derivative^[m]) P).natDegree ≤ P.natDegree - m :=
    Polynomial.natDegree_iterate_derivative P m
  have hzero : ((Polynomial.derivative^[m]) P).natDegree = 0 := by
    omega
  exact Polynomial.eq_C_of_natDegree_eq_zero hzero

/-- Pointwise version of the s>m endpoint, needed for interval sup bounds. -/
theorem markov_derivative_eval_zero_above_degree
    (P : Polynomial ℝ) (m s : ℕ)
    (hdegree : P.natDegree ≤ m) (hsm : m < s) (x : ℝ) :
    ((Polynomial.derivative^[s]) P).eval x = 0 := by
  rw [markov_derivative_zero_above_degree P m s hdegree hsm]
  simp

#print axioms markov_product_le_degree_power
#print axioms markov_derivative_zero_above_degree
#print axioms markov_top_derivative_constant
#print axioms markov_derivative_eval_zero_above_degree

end RhAstraSynthesis
