import RhAstraSynthesis.PolynomialReciprocalMeasure
import Mathlib.Tactic

/-!
# Remez argument normalization on reciprocal-grid good sets

Formalizes the quantitative Chebyshev-argument bound (`≤ 1 + 2/L`) for the
good set `E = {t ∈ [0, 1/(L*m)] | |P(t)| ≤ B}` arising in reciprocal-lattice
sampling.
-/

open Set MeasureTheory

namespace RhAstraSynthesis

/--
The exact numerical reduction in the Remez argument.
If an interval has length 1/(L*m) and its good set has measure at least
1/(L*m+m), then the Chebyshev argument is bounded by 1+2/L.

This is an independent inequality over real numbers, with neither a polynomial
nor a classical Remez theorem assumed.
-/
theorem remez_argument_of_measure
    (L m e : ℝ) (hL : 0 < L) (hm : 0 < m)
    (hmeas : 1 / (L*m + m) ≤ e) :
    2 * (1 / (L*m)) / e - 1 ≤ 1 + 2 / L := by
  have hp : 0 < L*m := mul_pos hL hm
  have hsum : 0 < L*m + m := add_pos hp hm
  have he : 0 < e :=
    lt_of_lt_of_le (one_div_pos.mpr hsum) hmeas
  have hcoeff : 0 ≤ 2 + 2/L := by positivity
  have hident :
      2 * (1 / (L*m)) = (2 + 2/L) * (1 / (L*m + m)) := by
    field_simp [ne_of_gt hL, ne_of_gt hm, ne_of_gt hp, ne_of_gt hsum]
  have hscaled : 2 * (1 / (L*m)) ≤ (2 + 2/L) * e := by
    calc
      2 * (1 / (L*m)) = (2 + 2/L) * (1 / (L*m + m)) := hident
      _ ≤ (2 + 2/L) * e :=
        mul_le_mul_of_nonneg_left hmeas hcoeff
  have hdiv : 2 * (1 / (L*m)) / e ≤ 2 + 2/L :=
    (div_le_iff₀ he).2 hscaled
  linarith

/--
Bridge from the independently proven polynomial-specific measure theorem to
the exact Remez argument for reciprocal sampling. All hypotheses are explicit:
the degree bound and sample inequalities are the only polynomial inputs.
-/
theorem polynomial_reciprocal_remez_argument
    (P : Polynomial ℝ) (B : ℝ) (L m : ℕ)
    (hB : 0 < B) (hL : 0 < L) (hm : 0 < m)
    (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    2 * (1 / ((L*m : ℕ) : ℝ)) /
      volume.real {t : ℝ |
        t ∈ Icc (0 : ℝ) (1 / ((L*m : ℕ) : ℝ)) ∧ |P.eval t| ≤ B} - 1
      ≤ 1 + 2 / (L : ℝ) := by
  have hkm : 0 < L*m := Nat.mul_pos hL hm
  have hmeasure :=
    polynomial_reciprocal_good_measure P B (L*m) m hB hkm hdegree hsample
  have hmeasure' :
      1 / ((L : ℝ)*(m : ℝ) + (m : ℝ)) ≤
        volume.real {t : ℝ |
          t ∈ Icc (0 : ℝ) (1 / ((L*m : ℕ) : ℝ)) ∧ |P.eval t| ≤ B} := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hmeasure
  have hrealL : (0 : ℝ) < L := by exact_mod_cast hL
  have hrealm : (0 : ℝ) < m := by exact_mod_cast hm
  have result := remez_argument_of_measure
    (L : ℝ) (m : ℝ)
    (volume.real {t : ℝ |
      t ∈ Icc (0 : ℝ) (1 / ((L*m : ℕ) : ℝ)) ∧ |P.eval t| ≤ B})
    hrealL hrealm hmeasure'
  simpa only [Nat.cast_mul] using result

#print axioms remez_argument_of_measure
#print axioms polynomial_reciprocal_remez_argument

end RhAstraSynthesis
