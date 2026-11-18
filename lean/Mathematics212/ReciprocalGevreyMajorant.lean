import Mathematics212.GevreyMomentFactorial
import Mathematics212.RemezInequality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cubic geometric majorants for reciprocal Gevrey-1

This is the fixed-order analytic summation step, independent of polynomial
representation. Apply it to the weighted absolute Taylor coefficients once the
reciprocal-sample derivative estimate has been normalized to a geometric ratio.
It does not assert a remainder theorem or a fractional-grid extension.
-/

namespace Mathematics212

/-- A nonnegative sequence dominated by the reciprocal cubic-degree majorant
is summable, with an explicit Gevrey-1 bound. The index `n` represents degree
`m = n + 1`; in particular the order-zero case has no spurious degree-zero term.
The factor `64` is the product of the interval loss `8` and the factorial loss `8`.
-/
theorem cubic_geometric_gevrey_majorant
    (a : ℕ → ℝ) (s : ℕ) {C L σ : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (ha : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, a n ≤
      (C * (8 * L) ^ s / ((2 * s).factorial : ℝ)) *
        (((n + 1 : ℕ) : ℝ) ^ (3 * s) * σ ^ (n + 1))) :
    Summable a ∧ (∑' n, a n) ≤
      C / (1 - σ) * (64 * L / (1 - σ) ^ 3) ^ s * (s.factorial : ℝ) := by
  have hd : 0 < 1 - σ := sub_pos.mpr hσ1
  have hf : (0 : ℝ) < ((2 * s).factorial : ℝ) := by positivity
  let K : ℝ := C * (8 * L) ^ s / ((2 * s).factorial : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨hm, hmoment⟩ := geometric_power_moment (3 * s) hσ hσ1
  have hmajor := hm.mul_left K
  have hsum : Summable a := Summable.of_nonneg_of_le ha hbound hmajor
  refine ⟨hsum, ?_⟩
  calc
    (∑' n, a n) ≤ ∑' n : ℕ,
        K * (((n + 1 : ℕ) : ℝ) ^ (3 * s) * σ ^ (n + 1)) :=
      hsum.tsum_le_tsum hbound hmajor
    _ = K * (∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) ^ (3 * s) * σ ^ (n + 1)) :=
      by rw [tsum_mul_left]
    _ ≤ K * ((Nat.factorial (3 * s) : ℝ) / (1 - σ) ^ (3 * s + 1)) :=
      mul_le_mul_of_nonneg_left hmoment hK
    _ = (C / (1 - σ) * (8 * L / (1 - σ) ^ 3) ^ s) *
        ((Nat.factorial (3 * s) : ℝ) / ((2 * s).factorial : ℝ)) := by
      dsimp [K]
      rw [div_pow, pow_succ, pow_mul]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (C / (1 - σ) * (8 * L / (1 - σ) ^ 3) ^ s) *
        ((8 : ℝ) ^ s * (s.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (factorial_three_div_two_le_eight_factorial s)
        (by positivity)
    _ = C / (1 - σ) * (64 * L / (1 - σ) ^ 3) ^ s *
        (s.factorial : ℝ) := by
      have hp : (8 * L / (1 - σ) ^ 3) ^ s * (8 : ℝ) ^ s =
          (64 * L / (1 - σ) ^ 3) ^ s := by
        rw [← mul_pow]
        congr 1
        ring
      calc
        _ = C / (1 - σ) *
            ((8 * L / (1 - σ) ^ 3) ^ s * (8 : ℝ) ^ s) *
            (s.factorial : ℝ) := by ring
        _ = _ := by rw [hp]

/-- A finite geometric sum with a uniform exponential bound, including
order zero. The recurrence avoids dividing by `1-a`. -/
lemma finite_geometric_sum_le_add_one_pow (a : ℝ) (ha : 0 ≤ a) (p : ℕ) :
    (∑ s ∈ Finset.range p, a ^ s) ≤ (1 + a) ^ p := by
  have hrec (q : ℕ) : (∑ s ∈ Finset.range (q + 1), a ^ s) =
      1 + a * ∑ s ∈ Finset.range q, a ^ s := by
    induction q with
    | zero => simp
    | succ q hq =>
      rw [Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [hq, pow_succ]
      ring
  induction p with
  | zero => simp
  | succ p ih =>
    rw [hrec p, pow_succ]
    have hone : (1 : ℝ) ≤ (1 + a) ^ p := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left ih ha]

/-- Explicit finite Taylor-order summation. Together with the mixed moment
bound this leaves only one order-`p` factorial, with a base depending on `σ`
but not on `p`. -/
lemma finite_mixed_geometric_bound (p : ℕ) {σ : ℝ} (hσ1 : σ < 1) :
    (∑ s ∈ Finset.range p,
      (8 : ℝ) ^ s / (1 - σ) ^ (p + 2 * s + 1)) ≤
        1 / (1 - σ) * ((1 + 8 / (1 - σ) ^ 2) / (1 - σ)) ^ p := by
  let d : ℝ := 1 - σ
  have hd : 0 < d := sub_pos.mpr hσ1
  have heq (s : ℕ) : (8 : ℝ) ^ s / d ^ (p + 2 * s + 1) =
      (1 / d ^ (p + 1)) * (8 / d ^ 2) ^ s := by
    rw [div_pow, ← pow_mul]
    have hexp : p + 2 * s + 1 = (p + 1) + 2 * s := by omega
    rw [hexp, pow_add]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  change (∑ s ∈ Finset.range p, (8 : ℝ) ^ s / d ^ (p + 2 * s + 1)) ≤ _
  calc
    _ = (1 / d ^ (p + 1)) * ∑ s ∈ Finset.range p, (8 / d ^ 2) ^ s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => heq s)
    _ ≤ (1 / d ^ (p + 1)) * (1 + 8 / d ^ 2) ^ p :=
      mul_le_mul_of_nonneg_left
        (finite_geometric_sum_le_add_one_pow _ (by positivity) p) (by positivity)
    _ = _ := by
      change _ = 1 / d * ((1 + 8 / d ^ 2) / d) ^ p
      rw [div_pow, pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Mixed moments for the large-degree regime, with convergence certified.
The finite Taylor-order sum can use this bound separately for each `s < p`. -/
theorem mixed_geometric_gevrey_moment (p s : ℕ) (hs : s ≤ p)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    Summable (fun k : ℕ =>
      (((k + 1 : ℕ) : ℝ) ^ (p + 2 * s) * σ ^ (k + 1)) /
        ((2 * s).factorial : ℝ)) ∧
    (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (p + 2 * s) * σ ^ (k + 1)) /
      ((2 * s).factorial : ℝ)) ≤
        (8 : ℝ) ^ p * (p.factorial : ℝ) / (1 - σ) ^ (p + 2 * s + 1) := by
  obtain ⟨hm, hb⟩ := geometric_power_moment (p + 2 * s) hσ hσ1
  have hsum := hm.div_const ((2 * s).factorial : ℝ)
  refine ⟨hsum, ?_⟩
  rw [tsum_div_const]
  calc
    _ ≤ (((p + 2 * s).factorial : ℝ) / (1 - σ) ^ (p + 2 * s + 1)) /
        ((2 * s).factorial : ℝ) := div_le_div_of_nonneg_right hb (by positivity)
    _ = (((p + 2 * s).factorial : ℝ) / ((2 * s).factorial : ℝ)) /
        (1 - σ) ^ (p + 2 * s + 1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (factorial_mixed_moment_div_le p s hs)
      (by positivity)

/-- Normalize the exponential degree loss before summing over a family. -/
theorem reciprocal_exponential_weight (m : ℕ) (r R L : ℝ) :
    Real.exp (2 * (m : ℝ) / Real.sqrt L) * (1 / R) ^ m * r ^ m =
      ((r / R) * Real.exp (2 / Real.sqrt L)) ^ m := by
  have he : Real.exp (2 * (m : ℝ) / Real.sqrt L) =
      Real.exp (2 / Real.sqrt L) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, ← mul_pow, ← mul_pow]
  congr 1
  ring

/-- The sampled polynomial estimate, including derivative orders above the degree.
The radius may be zero; no hypothesis on the degree-zero polynomial is needed. -/
theorem polynomial_reciprocal_family_pointwise
    (P : ℕ → Polynomial ℝ) (m s L : ℕ) {C R r : ℝ}
    (hC : 0 < C) (hR : 0 < R) (hr : 0 ≤ r) (hL : 0 < L)
    (hm : 0 < m) (hdegree : (P m).natDegree ≤ m)
    (hsample : ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m) :
    |((Polynomial.derivative^[s]) (P m)).eval 0| / (s.factorial : ℝ) * r ^ m ≤
      (C * (8 * (L : ℝ)) ^ s / ((2 * s).factorial : ℝ)) *
        ((m : ℝ) ^ (3 * s) * ((r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ m) := by
  by_cases hs : s ≤ m
  · have hb := polynomial_reciprocal_sample_factorial_bound
      (P m) (C * (1 / R) ^ m) L m s (by positivity) hL hm hs hdegree hsample
      (x := 0) ⟨le_rfl, by positivity⟩
    have hw := mul_le_mul_of_nonneg_right hb (pow_nonneg hr m)
    refine hw.trans_eq ?_
    calc
      _ = (C * (8 * (L : ℝ)) ^ s / ((2 * s).factorial : ℝ)) *
          ((m : ℝ) ^ (3 * s) *
            (Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * (1 / R) ^ m * r ^ m)) := by ring
      _ = _ := by rw [reciprocal_exponential_weight]
  · have hz : (Polynomial.derivative^[s]) (P m) = 0 :=
      Polynomial.iterate_derivative_eq_zero (hdegree.trans_lt (Nat.lt_of_not_ge hs))
    rw [hz]
    simp only [Polynomial.eval_zero, abs_zero, zero_div, zero_mul]
    positivity

/-- Reciprocal samples for a degree-controlled polynomial family imply absolute
summability of every weighted Taylor order and an explicit Gevrey-1 bound.
This is a coefficient-series result, not a remainder or fractional-grid theorem. -/
theorem polynomial_reciprocal_family_gevrey
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
        (s.factorial : ℝ) := by
  apply cubic_geometric_gevrey_majorant _ s hC.le (Nat.cast_nonneg L)
    (mul_nonneg (div_nonneg hr hR.le) (Real.exp_pos _).le) hσ
  · intro n
    positivity
  · intro n
    exact polynomial_reciprocal_family_pointwise P (n + 1) s L hC hR hr hL
      (Nat.succ_pos n) (hdegree _ (Nat.succ_pos n)) (hsample _ (Nat.succ_pos n))

/-- Every strict subradius admits a positive natural Remez parameter. The
parameter depends only on the radii, not on the derivative order or family. -/
theorem exists_reciprocal_gevrey_parameter {R r : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) :
    ∃ L : ℕ, 0 < L ∧ (r / R) * Real.exp (2 / Real.sqrt (L : ℝ)) < 1 := by
  by_cases hr0 : r = 0
  · exact ⟨1, by norm_num, by simp [hr0]⟩
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hratio : 1 < R / r := (one_lt_div hrp).2 hrR
  have hlog : 0 < Real.log (R / r) := Real.log_pos hratio
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / Real.log (R / r))
  have hNp : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNnat : 0 < N := by exact_mod_cast hNp
  refine ⟨N ^ 2, pow_pos hNnat _, ?_⟩
  have hexponent : 2 / (N : ℝ) < Real.log (R / r) := by
    apply (div_lt_iff₀ hNp).2
    have := (div_lt_iff₀ hlog).1 hN
    nlinarith
  have he : Real.exp (2 / (N : ℝ)) < R / r := by
    rw [← Real.exp_log (div_pos hR hrp)]
    exact Real.exp_lt_exp.mpr hexponent
  rw [Nat.cast_pow, Real.sqrt_sq hNp.le]
  calc
    r / R * Real.exp (2 / (N : ℝ)) < r / R * (R / r) :=
      mul_lt_mul_of_pos_left he (div_pos hrp hR)
    _ = 1 := by field_simp [ne_of_gt hR, ne_of_gt hrp]

/-- All strict subradii, including zero, with one natural parameter working
simultaneously for every derivative order. This closes the radius quantifier
for coefficient series only; no Taylor remainder is asserted. -/
theorem polynomial_reciprocal_family_gevrey_all_radii
    (P : ℕ → Polynomial ℝ) {C R : ℝ}
    (hC : 0 < C) (hR : 0 < R)
    (hdegree : ∀ m, 0 < m → (P m).natDegree ≤ m)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m) :
    ∀ r : ℝ, 0 ≤ r → r < R → ∃ L : ℕ, 0 < L ∧
      (r / R) * Real.exp (2 / Real.sqrt (L : ℝ)) < 1 ∧ ∀ s : ℕ,
      Summable (fun n : ℕ =>
        |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
          (s.factorial : ℝ) * r ^ (n + 1)) ∧
      (∑' n : ℕ, |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
          (s.factorial : ℝ) * r ^ (n + 1)) ≤
        C / (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) *
          (64 * (L : ℝ) /
            (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ 3) ^ s *
          (s.factorial : ℝ) := by
  intro r hr hrR
  obtain ⟨L, hL, hσ⟩ := exists_reciprocal_gevrey_parameter hR hr hrR
  exact ⟨L, hL, hσ, fun s => polynomial_reciprocal_family_gevrey
    P s L hC hR hr hL hdegree hsample hσ⟩

end Mathematics212
