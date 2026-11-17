import RhAstraSynthesis.MainTheorems
import RhAstraSynthesis.GevreyMomentFactorial

/-!
# Statement Signatures and Examples

Self-contained Mathlib-type signatures for the headline theorems in
`RhAstraSynthesis`, paired with concrete examples checking that each theorem's
hypotheses hold simultaneously on non-degenerate inputs.
-/

namespace RhAstraSynthesis.TargetStatements

open MeasureTheory Set

section Signatures

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

/-- Exponential Remez bound when `|E| ≥ (b - a) / (1 + 1 / L)`. -/
theorem remez_exponential_inequality (P : _root_.Polynomial ℝ) (n : ℕ) {a b L B : ℝ}
    (hab : a < b) (hL : 0 < L) (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEsub : E ⊆ Set.Icc a b)
    (hEmeas : (b - a) / (1 + 1 / L) ≤ MeasureTheory.volume.real E)
    (hEbnd : ∀ t ∈ E, |P.eval t| ≤ B) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |P.eval x| ≤ Real.exp (2 * (n : ℝ) / Real.sqrt L) * B :=
  RhAstraSynthesis.remez_exponential_inequality P n hab hL hB hdeg hEm hEsub hEmeas hEbnd hx

/-- Combined measurable Remez and iterated Markov interior derivative bound on `[a, b]`. -/
theorem remez_markov_interior_derivative_bound (P : _root_.Polynomial ℝ) (n s : ℕ) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEsub : E ⊆ Set.Icc a b)
    (he_pos : 0 < MeasureTheory.volume.real E) (hEbnd : ∀ t ∈ E, |P.eval t| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |(Nat.iterate _root_.Polynomial.derivative s P).eval x| ≤
      (2 / (b - a)) ^ s *
        (∏ j ∈ Finset.range s, (((n - j : ℕ) : ℝ) ^ 2)) *
        ((_root_.Polynomial.Chebyshev.T ℝ n).eval
          (2 * (b - a) / MeasureTheory.volume.real E - 1) * B) :=
  RhAstraSynthesis.remez_markov_interior_derivative_bound P n s hab hB hdeg hEm hEsub he_pos hEbnd hx

/-- Factorial-strength uniform bound, with a half-interval `2^s` loss. -/
theorem reciprocal_interval_factorial_bound
    (P : Polynomial ℝ) (m s : ℕ) {L M x : ℝ}
    (hm : 0 < m) (hs : s ≤ m) (hL : 0 < L) (hM : 0 ≤ M)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Icc (0 : ℝ) (1 / (L * (m : ℝ))), |P.eval t| ≤ M)
    (hx : x ∈ Icc (0 : ℝ) (1 / (L * (m : ℝ)))) :
    |((Polynomial.derivative^[s]) P).eval x| / (s.factorial : ℝ) ≤
      M * (((8 * L) ^ s * (m : ℝ) ^ (3 * s)) / ((2 * s).factorial : ℝ)) :=
  RhAstraSynthesis.markov_reciprocal_interval_factorial_bound P m s hm hs hL hM
    hdeg hbounded hx

/-- Reciprocal samples imply uniform exponential control on the shrinking interval. -/
theorem reciprocal_sample_exponential_bound
    (P : Polynomial ℝ) (B : ℝ) (L m : ℕ)
    (hB : 0 < B) (hL : 0 < L) (hm : 0 < m)
    (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    ∀ x ∈ Icc (0 : ℝ) (1 / ((L : ℝ) * (m : ℝ))),
      |P.eval x| ≤ Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * B :=
  RhAstraSynthesis.polynomial_reciprocal_remez_exponential_bound
    P B L m hB hL hm hdegree hsample

/-- Reciprocal Gevrey-1 polynomial input: all orders up to the degree bound,
uniformly over the closed shrinking interval, with the `(8L)^s` loss. -/
theorem reciprocal_sample_factorial_bound
    (P : Polynomial ℝ) (B : ℝ) (L m s : ℕ)
    (hB : 0 < B) (hL : 0 < L) (hm : 0 < m) (hs : s ≤ m)
    (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / ((L : ℝ) * (m : ℝ)))) :
    |((Polynomial.derivative^[s]) P).eval x| / (s.factorial : ℝ) ≤
      (Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * B) *
        (((8 * (L : ℝ)) ^ s * (m : ℝ) ^ (3 * s)) / ((2 * s).factorial : ℝ)) :=
  RhAstraSynthesis.polynomial_reciprocal_sample_factorial_bound
    P B L m s hB hL hm hs hdegree hsample hx

/-- Uniform positive-index geometric moment estimate, with convergence included. -/
theorem geometric_power_moment_bound (j : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ j * σ ^ (n + 1)) ∧
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ j * σ ^ (n + 1)) ≤
        (j.factorial : ℝ) / (1 - σ) ^ (j + 1) :=
  RhAstraSynthesis.geometric_power_moment j hσ hσ1

/-- Fixed-order analytic bridge; the pointwise cubic geometric estimate is
an input, not a polynomial-family or remainder conclusion. -/
theorem reciprocal_gevrey_majorant
    (a : ℕ → ℝ) (s : ℕ) {C L σ : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (ha : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, a n ≤
      (C * (8 * L) ^ s / ((2 * s).factorial : ℝ)) *
        (((n + 1 : ℕ) : ℝ) ^ (3 * s) * σ ^ (n + 1))) :
    Summable a ∧ (∑' n, a n) ≤
      C / (1 - σ) * (64 * L / (1 - σ) ^ 3) ^ s * (s.factorial : ℝ) :=
  RhAstraSynthesis.cubic_geometric_gevrey_majorant a s hC hL hσ hσ1 ha hbound

/-- Polynomial-family specialization: the majorant is derived from samples. -/
theorem reciprocal_polynomial_family_gevrey
    (P : ℕ → Polynomial ℝ) (s L : ℕ) {C R r : ℝ}
    (hC : 0 < C) (hR : 0 < R) (hr : 0 ≤ r) (hL : 0 < L)
    (hdegree : ∀ m, 0 < m → (P m).natDegree ≤ m)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m)
    (hσ : (r / R) * Real.exp (2 / Real.sqrt (L : ℝ)) < 1) :
    Summable (fun n : ℕ =>
      |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
        (s.factorial : ℝ) * r ^ (n + 1)) ∧
      (∑' n : ℕ, |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
        (s.factorial : ℝ) * r ^ (n + 1)) ≤
      C / (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) *
        (64 * (L : ℝ) /
          (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ 3) ^ s *
        (s.factorial : ℝ) :=
  RhAstraSynthesis.polynomial_reciprocal_family_gevrey P s L hC hR hr hL
    hdegree hsample hσ

end Signatures

section Examples

/-- A nonconstant family with a nonzero first derivative at every index and
positive radius: `P_m = X`, `C = R = L = 1`, `r = exp(-2)/2`, `σ = 1/2`. -/
example :
    Summable (fun n : ℕ =>
      |((Polynomial.derivative^[1]) (Polynomial.X : Polynomial ℝ)).eval 0| /
        (Nat.factorial 1 : ℝ) * (Real.exp (-2) / 2) ^ (n + 1)) ∧
      (∑' n : ℕ,
        |((Polynomial.derivative^[1]) (Polynomial.X : Polynomial ℝ)).eval 0| /
          (Nat.factorial 1 : ℝ) * (Real.exp (-2) / 2) ^ (n + 1)) ≤ 1024 := by
  have he : Real.exp (-2) / 2 * Real.exp 2 = (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have h := reciprocal_polynomial_family_gevrey
    (fun _ => (Polynomial.X : Polynomial ℝ)) 1 1
    (C := 1) (R := 1) (r := Real.exp (-2) / 2)
    (by norm_num) (by norm_num) (by positivity) (by norm_num)
    (fun m hm => by simpa using Nat.succ_le_of_lt hm)
    (fun m hm k hk => by
      have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast Nat.succ_le_of_lt hk
      simp only [Polynomial.eval_X, div_one, one_pow, mul_one]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ))]
      exact (div_le_one (by positivity)).2 hkreal)
    (by norm_num only [Nat.cast_one, Real.sqrt_one, div_one]; rw [he]; norm_num)
  norm_num only [Nat.cast_one, Real.sqrt_one, div_one, Nat.factorial_one] at h
  rw [he] at h
  norm_num at h ⊢
  exact h

/-- A nonzero second moment at ratio `1/2`; the bound is `2! * 2^3 = 16`. -/
example :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n + 1)) ∧
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n + 1)) ≤ 16 := by
  have h := geometric_power_moment_bound 2 (σ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Order zero starts at one: its value at ratio `1/2` is one, not two. -/
example : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 0 * (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
  have h := RhAstraSynthesis.geometric_power_moment_zero
    (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Nonconstant sampled witness with a nonzero highest derivative:
`P(t) = t^2`, `B = 1`, `L = 2`, `m = s = 2`, at the midpoint `1/8`. -/
example :
    |((Polynomial.derivative^[2]) ((Polynomial.X : Polynomial ℝ) ^ 2)).eval (1 / 8)| /
        (Nat.factorial 2 : ℝ) ≤
      (Real.exp (2 * (2 : ℝ) / Real.sqrt (2 : ℝ)) * 1) *
        (((8 * (2 : ℝ)) ^ 2 * (2 : ℝ) ^ (3 * 2)) / ((2 * 2).factorial : ℝ)) := by
  apply reciprocal_sample_factorial_bound _ 1 2 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp)
  · intro n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
    have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have hle : (1 : ℝ) / (n : ℝ) ≤ 1 := (div_le_one (by positivity)).2 hnreal
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  · norm_num

/-- A genuine second derivative at the midpoint: `P(t) = t^2`, `m = 2`, `L = M = 1`. -/
example :
    |((Polynomial.derivative^[2]) ((Polynomial.X : Polynomial ℝ) ^ 2)).eval (1 / 4)| /
        (Nat.factorial 2 : ℝ) ≤
      (1 : ℝ) * (((8 * 1) ^ 2 * (2 : ℝ) ^ (3 * 2)) / ((2 * 2).factorial : ℝ)) := by
  apply reciprocal_interval_factorial_bound _ 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp)
  · intro t ht
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    rw [abs_of_nonneg (sq_nonneg t)]
    norm_num at ht
    nlinarith [ht.1, ht.2]
  · norm_num

/-- Polynomial `P(x) = x` of degree `1` satisfies the Markov interior bound at `x = 1`. -/
example : |(Polynomial.derivative (Polynomial.X : Polynomial ℝ)).eval 1| ≤ ((1 : ℕ) : ℝ) ^ 2 * 1 :=
  markov_interior_derivative Polynomial.X 1 (by norm_num) (by simp)
    (fun t ht => by simp only [Polynomial.eval_X]; exact abs_le.mpr ⟨ht.1, ht.2⟩)
    ⟨by norm_num, by norm_num⟩

/-- Constant polynomial `P(x) = 1` satisfies the reciprocal good-measure hypotheses for `k = 1, m = 1`. -/
example : (1 : ℝ) / (↑(1 + 1 : ℕ) : ℝ) ≤
    volume.real {t : ℝ | t ∈ Icc 0 (1 / ((1 : ℕ) : ℝ)) ∧ |(1 : Polynomial ℝ).eval t| ≤ 1} :=
  reciprocal_good_set_measure (1 : Polynomial ℝ) 1 1 1 (by norm_num) (by norm_num)
    (by simp) (fun _ _ => by simp)

/-- Parameters `m = 1, L = 1, e = 1/2` satisfy the Remez–Chebyshev envelope hypotheses. -/
example : (Polynomial.Chebyshev.T ℝ (1 : ℤ)).eval (2 * (1 / ((1 : ℝ) * ((1 : ℕ) : ℝ))) / (1 / 2 : ℝ) - 1) ≤
    Real.exp (2 * ((1 : ℕ) : ℝ) / Real.sqrt (1 : ℝ)) :=
  remez_chebyshev_envelope (m := 1) (L := 1) (e := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Parameters `d = 6, n = 5` satisfy `coprime_mobius_factorization`. -/
example :
    (∑ a ∈ (5 : ℕ).divisorsAntidiagonal,
      (ArithmeticFunction.moebius a.1 : ℝ) * actualCoprimeKernel 6 a.2) =
      CoprimeMobius.f 5 * (if (5 : ℕ).Coprime 6 then 1 else 0) :=
  coprime_mobius_factorization 6 5 (by norm_num)

/-- Parameter `N = 6` satisfies `harmonic_moebius_bound`. -/
example : |∑ n ∈ Finset.Ioc 0 6, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 :=
  harmonic_moebius_bound 6 (by norm_num)

/-- Point `s = 1/2 + I` satisfies `tent_mellin_nonvanishing`. -/
example : mellin TentMellin.tent ((1 / 2 : ℂ) + Complex.I) ≠ 0 :=
  tent_mellin_nonvanishing ((1 / 2 : ℂ) + Complex.I)
    (by norm_num [Complex.add_re]) (by norm_num [Complex.add_re])

/-- Data `G(t) = 0`, `C = 1, δ = 1, K = 2` satisfy `log_decay_tail_integrable`. -/
example :
    IntegrableOn (fun t : ℝ => (0 : ℝ) / t) (Ioi 2) ∧
      |∫ t in Ioi (2 : ℝ), (0 : ℝ) / t| ≤ 1 / (1 * (Real.log 2) ^ (1 : ℝ)) :=
  log_decay_tail_integrable (G := fun _ => (0 : ℝ)) (C := 1) (δ := 1) (K := 2)
    measurable_const (by norm_num) (by norm_num) (by norm_num) (fun t ht => by
      have hpos : 0 < Real.log t := Real.log_pos (by linarith)
      simp only [abs_zero]
      positivity)

/-- Polynomial `P(x) = x` bounded by `1` on `E = [0, 1] ⊆ [0, 2]` satisfies `remez_inequality` at `x = 2`. -/
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

/-- Polynomial `P(x) = x` bounded by `1` on `E = [0, 1] ⊆ [0, 2]` satisfies the combined derivative bound at `x = 2`. -/
example :
    |(Nat.iterate _root_.Polynomial.derivative 1 (_root_.Polynomial.X : _root_.Polynomial ℝ)).eval (2 : ℝ)| ≤
      (2 / ((2 : ℝ) - 0)) ^ 1 *
        (∏ j ∈ Finset.range 1, (((1 - j : ℕ) : ℝ) ^ 2)) *
        ((_root_.Polynomial.Chebyshev.T ℝ 1).eval
          (2 * ((2 : ℝ) - 0) / MeasureTheory.volume.real (Set.Icc (0 : ℝ) 1) - 1) * 1) :=
  remez_markov_interior_derivative_bound _root_.Polynomial.X 1 1 (by norm_num) (by norm_num)
    (by simp) measurableSet_Icc (Set.Icc_subset_Icc_right (by norm_num))
    (by rw [Real.volume_real_Icc_of_le (by norm_num)]; norm_num)
    (fun t ht => by
      simp only [_root_.Polynomial.eval_X]
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    ⟨by norm_num, by norm_num⟩

end Examples

#print axioms reciprocal_polynomial_family_gevrey
#print axioms RhAstraSynthesis.polynomial_reciprocal_family_pointwise
#print axioms reciprocal_interval_factorial_bound
#print axioms geometric_power_moment_bound
#print axioms RhAstraSynthesis.geometric_power_moment_zero
#print axioms reciprocal_sample_exponential_bound
#print axioms reciprocal_sample_factorial_bound
#print axioms bernstein_van_der_corput_schaake
#print axioms markov_interior_derivative
#print axioms reciprocal_good_set_measure
#print axioms remez_chebyshev_envelope
#print axioms remez_inequality
#print axioms remez_exponential_inequality
#print axioms remez_markov_interior_derivative_bound
#print axioms coprime_mobius_factorization
#print axioms harmonic_moebius_bound
#print axioms tent_mellin_nonvanishing
#print axioms log_decay_tail_integrable

end RhAstraSynthesis.TargetStatements
