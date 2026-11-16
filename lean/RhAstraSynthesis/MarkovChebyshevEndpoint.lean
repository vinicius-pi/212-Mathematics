import RhAstraSynthesis.MarkovAffineTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Tactic

/-!
# Analytic Markov endpoint inequality from Mathlib's Chebyshev extremal theorem

Applies Mathlib's `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`
to `P` and `-P` to obtain a two-sided absolute bound `|(P^(s)).eval x| ≤ (T_m^(s)).eval x`
for every `x ≥ 1` and every real polynomial of degree `≤ m` bounded by `1` on `[-1, 1]`,
specializing to `x = 1` in `markov_chebyshev_derivative_abs_at_one`.
-/

namespace RhAstraSynthesis

open Polynomial

/-- The sharp Chebyshev derivative envelope to the right of [-1,1].
This is a direct application of a fully proved theorem in pinned Mathlib. -/
theorem markov_chebyshev_derivative_upper_outside
    (P : Polynomial ℝ) (m s : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1) :
    ((Polynomial.derivative^[s]) P).eval x ≤
      ((Polynomial.derivative^[s]) (Polynomial.Chebyshev.T ℝ m)).eval x := by
  exact Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (n := m) (P := P) (k := s) (x := x) hx hdeg hbounded

/-- Absolute derivative bound on the entire right ray [1,∞), including
the endpoint x=1; the same upper bound applies to P and -P.
This does not assert the Markov derivative bound at any interior point. -/
theorem markov_chebyshev_derivative_abs_outside
    (P : Polynomial ℝ) (m s : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1) :
    |((Polynomial.derivative^[s]) P).eval x| ≤
      ((Polynomial.derivative^[s]) (Polynomial.Chebyshev.T ℝ m)).eval x := by
  have hright :=
    markov_chebyshev_derivative_upper_outside P m s x hx hdeg hbounded
  have hnegdeg : (-P).degree ≤ m := by
    simpa only [Polynomial.degree_neg] using hdeg
  have hnegbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(-P).eval t| ≤ 1 := by
    intro t ht
    simpa only [Polynomial.eval_neg, abs_neg] using hbounded t ht
  have hleft :=
    markov_chebyshev_derivative_upper_outside (-P) m s x hx hnegdeg hnegbounded
  have hleft' :
      -((Polynomial.derivative^[s]) P).eval x ≤
        ((Polynomial.derivative^[s]) (Polynomial.Chebyshev.T ℝ m)).eval x := by
    simpa only [Polynomial.iterate_derivative_neg, Polynomial.eval_neg] using hleft
  exact abs_le.mpr ⟨by linarith, hright⟩

/-- In particular, the higher derivative of a bounded real polynomial
at the right endpoint never exceeds the corresponding Chebyshev endpoint. -/
theorem markov_chebyshev_derivative_abs_at_one
    (P : Polynomial ℝ) (m s : ℕ)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1) :
    |((Polynomial.derivative^[s]) P).eval 1| ≤
      ((Polynomial.derivative^[s]) (Polynomial.Chebyshev.T ℝ m)).eval 1 := by
  exact markov_chebyshev_derivative_abs_outside P m s 1 (by norm_num) hdeg hbounded

end RhAstraSynthesis
