import RhAstraSynthesis.MainTheorems

/-!
# Target Statements & Non-Vacuity Witnesses

Standalone mathematician-facing specification targets for `RhAstraSynthesis`,
paired with executable kernel witnesses demonstrating that each headline theorem's
hypothesis bundle is jointly satisfiable on concrete non-degenerate objects.

Design rule: every public target uses canonical Mathlib types (`Polynomial ℝ`, `ℂ`,
`ArithmeticFunction ℝ`, `MeasureTheory.volume`) without internal proof-search helpers,
pre-empting vacuous implication (`False → P`) and definition drift.
-/

namespace RhAstraSynthesis.TargetStatements

open MeasureTheory Set

section FrozenTargets

theorem bernstein_van_der_corput_schaake
    (P : Polynomial ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hdeg : P.natDegree ≤ n)
    (hbounded : ∀ t ∈ Icc (-1 : ℝ) 1, |P.eval t| ≤ B) (θ : ℝ) :
    (n : ℝ) ^ 2 * (P.eval (Real.cos θ)) ^ 2 +
        ((Polynomial.derivative P).eval (Real.cos θ) * Real.sin θ) ^ 2 ≤
      (n : ℝ) ^ 2 * B ^ 2 :=
  RhAstraSynthesis.van_der_corput_schaake P n hB hdeg hbounded θ

theorem markov_interior_derivative
    (P : Polynomial ℝ) (n : ℕ) {B x : ℝ} (hB : 0 ≤ B)
    (hdeg : P.natDegree ≤ n)
    (hbounded : ∀ t ∈ Icc (-1 : ℝ) 1, |P.eval t| ≤ B)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Polynomial.derivative P).eval x| ≤ (n : ℝ) ^ 2 * B :=
  RhAstraSynthesis.markov_interior_derivative_abs_le P n hB hdeg hbounded hx

theorem reciprocal_good_set_measure
    (P : Polynomial ℝ) (B : ℝ) (k m : ℕ) (hB : 0 < B)
    (hk : 0 < k) (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    (1 : ℝ) / (↑(k + m) : ℝ) ≤
      volume.real {t : ℝ | t ∈ Icc 0 (1 / (k : ℝ)) ∧ |P.eval t| ≤ B} :=
  RhAstraSynthesis.polynomial_reciprocal_good_measure P B k m hB hk hdegree hsample

theorem remez_chebyshev_envelope
    (m : ℕ) {L e : ℝ} (hL : 0 < L) (hm : 0 < (m : ℝ))
    (hmeas_low : 1 / (L * (m : ℝ) + (m : ℝ)) ≤ e)
    (hmeas_high : e ≤ 1 / (L * (m : ℝ))) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (2 * (1 / (L * (m : ℝ))) / e - 1) ≤
      Real.exp (2 * (m : ℝ) / Real.sqrt L) :=
  RhAstraSynthesis.remez_chebyshev_T_le_exp m hL hm hmeas_low hmeas_high

theorem coprime_mobius_factorization (d n : ℕ) (hn : 0 < n) :
    (∑ a ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius a.1 : ℝ) * actualCoprimeKernel d a.2) =
      CoprimeMobius.f n * (if n.Coprime d then 1 else 0) :=
  RhAstraSynthesis.actual_coprime_mobius_factorization d n hn

theorem harmonic_moebius_bound (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 :=
  RhAstraSynthesis.moebius_harmonic_abs_le_one N hN

theorem tent_mellin_nonvanishing (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin TentMellin.tent s ≠ 0 :=
  TentMellin.tent_mellin_ne_zero s h0 h1

theorem log_decay_tail_integrable
    {G : ℝ → ℝ} {C δ K : ℝ} (hGm : Measurable G)
    (hC : 0 ≤ C) (hδ : 0 < δ) (hK : 2 ≤ K)
    (hG : ∀ t, 2 ≤ t → |G t| ≤ C / (Real.log t) ^ (1 + δ)) :
    IntegrableOn (fun t => G t / t) (Ioi K) ∧
      |∫ t in Ioi K, G t / t| ≤ C / (δ * (Real.log K) ^ δ) :=
  RhAstraSynthesis.log_decay_integrable_and_tail_bound hGm hC hδ hK hG

/-- Measurable equioscillation Remez inequality on any compact interval `[a, b]`. -/
theorem remez_inequality (P : _root_.Polynomial ℝ) (n : ℕ) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEsub : E ⊆ Set.Icc a b)
    (he_pos : 0 < MeasureTheory.volume.real E) (hEbnd : ∀ t ∈ E, |P.eval t| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |P.eval x| ≤
      (_root_.Polynomial.Chebyshev.T ℝ n).eval
        (2 * (b - a) / MeasureTheory.volume.real E - 1) * B :=
  RhAstraSynthesis.remez_inequality P n hab hB hdeg hEm hEsub he_pos hEbnd hx

end FrozenTargets

/-- Polynomial sublevel sets remain measurable after restriction to a measurable set. -/
theorem measurable_polynomial_good_set (P : Polynomial ℝ) (B : ℝ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet {t : ℝ | t ∈ E ∧ |P.eval t| ≤ B} :=
  hE.inter (measurableSet_le P.continuous.abs.measurable measurable_const)

/-- The good set for the nonconstant polynomial `X` on `[-1, 1]` is measurable. -/
example : MeasurableSet
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1} :=
  measurable_polynomial_good_set Polynomial.X 1 measurableSet_Icc

example : (1 / 2 : ℝ) ∈
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1} := by
  norm_num

/-- Polynomial good sets are closed when the restricting set is closed. -/
theorem isClosed_polynomial_good_set (P : Polynomial ℝ) (B : ℝ)
    {E : Set ℝ} (hE : IsClosed E) :
    IsClosed {t : ℝ | t ∈ E ∧ |P.eval t| ≤ B} :=
  hE.inter (isClosed_le P.continuous.abs continuous_const)

example : IsClosed
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1 / 2} :=
  isClosed_polynomial_good_set Polynomial.X (1 / 2) isClosed_Icc

example : (1 / 4 : ℝ) ∈
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1 / 2} := by
  norm_num

example : (3 / 4 : ℝ) ∉
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1 / 2} := by
  norm_num

/-- Polynomial good sets inside compact sets are compact. -/
theorem isCompact_polynomial_good_set (P : Polynomial ℝ) (B : ℝ)
    {E : Set ℝ} (hE : IsCompact E) :
    IsCompact {t : ℝ | t ∈ E ∧ |P.eval t| ≤ B} :=
  hE.inter_right (isClosed_le P.continuous.abs continuous_const)

example : IsCompact
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1 / 2} :=
  isCompact_polynomial_good_set Polynomial.X (1 / 2) isCompact_Icc

example : (1 / 4 : ℝ) ∈
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1 / 2} := by
  norm_num

example : (3 / 4 : ℝ) ∉
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧ |(Polynomial.X : Polynomial ℝ).eval t| ≤ 1 / 2} := by
  norm_num

#print axioms isCompact_polynomial_good_set
#print axioms isClosed_polynomial_good_set
#print axioms measurable_polynomial_good_set

section NonVacuityWitnesses

/-- Non-trivial polynomial `P(x) = x` of degree `1` satisfies the Markov interior hypotheses at `x = 1`. -/
example : |(Polynomial.derivative (Polynomial.X : Polynomial ℝ)).eval 1| ≤ ((1 : ℕ) : ℝ) ^ 2 * 1 :=
  markov_interior_derivative Polynomial.X 1 (by norm_num) (by simp)
    (fun t ht => by simp only [Polynomial.eval_X]; exact abs_le.mpr ⟨ht.1, ht.2⟩)
    ⟨by norm_num, by norm_num⟩

/-- Constant polynomial `P(x) = 1` satisfies the reciprocal good-measure hypotheses for `k = 1, m = 1`. -/
example : (1 : ℝ) / (↑(1 + 1 : ℕ) : ℝ) ≤
    volume.real {t : ℝ | t ∈ Icc 0 (1 / ((1 : ℕ) : ℝ)) ∧ |(1 : Polynomial ℝ).eval t| ≤ 1} :=
  reciprocal_good_set_measure (1 : Polynomial ℝ) 1 1 1 (by norm_num) (by norm_num)
    (by simp) (fun _ _ => by simp)

/-- Witness `m = 1, L = 1, e = 1/2` satisfies the Remez–Chebyshev hypothesis interval. -/
example : (Polynomial.Chebyshev.T ℝ (1 : ℤ)).eval (2 * (1 / ((1 : ℝ) * ((1 : ℕ) : ℝ))) / (1 / 2 : ℝ) - 1) ≤
    Real.exp (2 * ((1 : ℕ) : ℝ) / Real.sqrt (1 : ℝ)) :=
  remez_chebyshev_envelope (m := 1) (L := 1) (e := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Witness `d = 6, n = 5` is non-vacuous and coprime in `coprime_mobius_factorization`. -/
example :
    (∑ a ∈ (5 : ℕ).divisorsAntidiagonal,
      (ArithmeticFunction.moebius a.1 : ℝ) * actualCoprimeKernel 6 a.2) =
      CoprimeMobius.f 5 * (if (5 : ℕ).Coprime 6 then 1 else 0) :=
  coprime_mobius_factorization 6 5 (by norm_num)

/-- Witness `N = 6` satisfies the uniform harmonic Möbius hypothesis `1 ≤ N`. -/
example : |∑ n ∈ Finset.Ioc 0 6, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 :=
  harmonic_moebius_bound 6 (by norm_num)

/-- Witness `s = 1/2 + I` satisfies `0 < s.re < 1` in `tent_mellin_nonvanishing`. -/
example : mellin TentMellin.tent ((1 / 2 : ℂ) + Complex.I) ≠ 0 :=
  tent_mellin_nonvanishing ((1 / 2 : ℂ) + Complex.I)
    (by norm_num [Complex.add_re]) (by norm_num [Complex.add_re])

/-- Witness `G(t) = 0` (`C = 1, δ = 1, K = 2`) satisfies `log_decay_tail_integrable`. -/
example :
    IntegrableOn (fun t : ℝ => (0 : ℝ) / t) (Ioi 2) ∧
      |∫ t in Ioi (2 : ℝ), (0 : ℝ) / t| ≤ 1 / (1 * (Real.log 2) ^ (1 : ℝ)) :=
  log_decay_tail_integrable (G := fun _ => (0 : ℝ)) (C := 1) (δ := 1) (K := 2)
    measurable_const (by norm_num) (by norm_num) (by norm_num) (fun t ht => by
      have hpos : 0 < Real.log t := Real.log_pos (by linarith)
      simp only [abs_zero]
      positivity)

end NonVacuityWitnesses

#print axioms bernstein_van_der_corput_schaake
#print axioms markov_interior_derivative
#print axioms reciprocal_good_set_measure
#print axioms remez_chebyshev_envelope
#print axioms coprime_mobius_factorization
#print axioms harmonic_moebius_bound
#print axioms tent_mellin_nonvanishing
#print axioms log_decay_tail_integrable

example :
    |(_root_.Polynomial.X : _root_.Polynomial ℝ).eval (2 : ℝ)| ≤
      (_root_.Polynomial.Chebyshev.T ℝ 1).eval
        (2 * ((2 : ℝ) - 0) / MeasureTheory.volume.real (Set.Icc (0 : ℝ) 1) - 1) * 1 :=
  remez_inequality _root_.Polynomial.X 1 (by norm_num) (by norm_num)
    (by simp) measurableSet_Icc (Set.Icc_subset_Icc_right (by norm_num))
    (by rw [Real.volume_real_Icc_of_le (by norm_num)]; norm_num)
    (fun t ht => by
      simp only [_root_.Polynomial.eval_X]
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    ⟨by norm_num, by norm_num⟩

#print axioms remez_inequality

end RhAstraSynthesis.TargetStatements
