import RhAstraSynthesis.ReciprocalRemainderSeries
import RhAstraSynthesis.ReciprocalCoefficientProfile

/-!
# Complex reciprocal Gevrey-1 expansion

The explicit constant `1` is retained on both sides of the expansion. Thus the
full order-zero profile is `1 + reciprocalCoefficientProfile P 0`; the positive
order profiles are unchanged. This is the reciprocal-sample theorem, not the
fractional-sample generalization.
-/

noncomputable section
namespace RhAstraSynthesis

/-- Sampled series, indexed by positive polynomial degree. -/
def reciprocalSampledFunction (P : ℕ → Polynomial ℝ) (n : ℕ) (u : ℂ) : ℂ :=
  1 + ∑' k : ℕ, ((P (k + 1)).eval (1 / (n : ℝ)) : ℂ) * u ^ (k + 1)

/-- Truncation with the degree-zero constant written explicitly. -/
def reciprocalProfileExpansion (P : ℕ → Polynomial ℝ) (n p : ℕ) (u : ℂ) : ℂ :=
  1 + ∑ s ∈ Finset.range p,
    reciprocalCoefficientProfile P s u * ((1 / (n : ℝ) : ℝ) : ℂ) ^ s

/-- Original sample bounds alone give absolute convergence on the open disk. -/
theorem reciprocal_sampled_summable
    (P : ℕ → Polynomial ℝ) (n : ℕ) {C R : ℝ} {u : ℂ}
    (hR : 0 < R) (hn : 0 < n) (hu : ‖u‖ < R)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m) :
    Summable (fun k : ℕ =>
      ‖((P (k + 1)).eval (1 / (n : ℝ)) : ℂ) * u ^ (k + 1)‖) := by
  have hratio : ‖u‖ / R < 1 := (div_lt_one hR).2 hu
  have hg := (geometric_power_moment 0 (div_nonneg (norm_nonneg u) hR.le) hratio).1
  simp only [pow_zero, one_mul] at hg
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hg.mul_left C)
  intro k
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (C * (1 / R) ^ (k + 1)) * ‖u‖ ^ (k + 1) :=
      mul_le_mul_of_nonneg_right (hsample (k + 1) (Nat.succ_pos k) n hn)
        (by positivity)
    _ = C * (‖u‖ / R) ^ (k + 1) := by
      simp only [div_eq_mul_inv, mul_pow, one_pow, one_mul]
      ring

/-- The finite Taylor sum may be interchanged with the degree series because
all coefficient-profile series converge. The two explicit constants cancel. -/
theorem reciprocal_complex_remainder_identity
    (P : ℕ → Polynomial ℝ) (n p : ℕ) (u : ℂ)
    (hsample : Summable (fun k : ℕ =>
      ((P (k + 1)).eval (1 / (n : ℝ)) : ℂ) * u ^ (k + 1)))
    (hprofile : ∀ s, Summable (fun k => reciprocalProfileTerm P s k u)) :
    reciprocalSampledFunction P n u - reciprocalProfileExpansion P n p u =
      ∑' k : ℕ, (((P (k + 1)).eval (1 / (n : ℝ)) -
        ∑ s ∈ Finset.range p, (P (k + 1)).coeff s * (1 / (n : ℝ)) ^ s : ℝ) : ℂ) *
          u ^ (k + 1) := by
  have hf (s : ℕ) (_hs : s ∈ Finset.range p) :=
    (hprofile s).mul_right (((1 / (n : ℝ) : ℝ) : ℂ) ^ s)
  have hfinite := summable_sum hf
  have hexchange :
      (∑' k : ℕ, ∑ s ∈ Finset.range p,
        reciprocalProfileTerm P s k u * ((1 / (n : ℝ) : ℝ) : ℂ) ^ s) =
      ∑ s ∈ Finset.range p,
        reciprocalCoefficientProfile P s u * ((1 / (n : ℝ) : ℝ) : ℂ) ^ s := by
    rw [Summable.tsum_finsetSum hf]
    simp only [tsum_mul_right, reciprocalCoefficientProfile]
  calc
    _ = (∑' k : ℕ, ((P (k + 1)).eval (1 / (n : ℝ)) : ℂ) * u ^ (k + 1)) -
        (∑' k : ℕ, ∑ s ∈ Finset.range p,
          reciprocalProfileTerm P s k u * ((1 / (n : ℝ) : ℝ) : ℂ) ^ s) := by
      rw [hexchange]
      unfold reciprocalSampledFunction reciprocalProfileExpansion
      ring
    _ = ∑' k : ℕ, (((P (k + 1)).eval (1 / (n : ℝ)) : ℂ) * u ^ (k + 1) -
        ∑ s ∈ Finset.range p,
          reciprocalProfileTerm P s k u * ((1 / (n : ℝ) : ℝ) : ℂ) ^ s) :=
      (hsample.tsum_sub hfinite).symm
    _ = _ := by
      apply tsum_congr
      intro k
      simp only [reciprocalProfileTerm, reciprocal_normalized_derivative_coeff]
      push_cast
      simp only [sub_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Full reciprocal Gevrey-1 remainder from degree and sample hypotheses.
One parameter is selected for each closed subdisk before the sample index,
truncation order, or complex point. No remainder summability is assumed. -/
theorem polynomial_reciprocal_gevrey_expansion
    (P : ℕ → Polynomial ℝ) {C R : ℝ}
    (hC : 0 < C) (hR : 0 < R)
    (hdegree : ∀ m, 0 < m → (P m).natDegree ≤ m)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m) :
    ∀ r : ℝ, 0 ≤ r → r < R → ∃ L : ℕ, 0 < L ∧
      (r / R) * Real.exp (2 / Real.sqrt (L : ℝ)) < 1 ∧
      ∀ n p : ℕ, 0 < n → 0 < p → ∀ u : ℂ, ‖u‖ ≤ r →
        Summable (fun k : ℕ =>
          ‖((P (k + 1)).eval (1 / (n : ℝ)) : ℂ) * u ^ (k + 1)‖) ∧
        reciprocalSampledFunction P n u - reciprocalProfileExpansion P n p u =
          (∑' k : ℕ, (((P (k + 1)).eval (1 / (n : ℝ)) -
            ∑ s ∈ Finset.range p, (P (k + 1)).coeff s * (1 / (n : ℝ)) ^ s : ℝ) : ℂ) *
              u ^ (k + 1)) ∧
        ‖reciprocalSampledFunction P n u - reciprocalProfileExpansion P n p u‖ ≤
          3 * C / (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) *
            (72 * (L : ℝ) /
              (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ 3) ^ p *
                (p.factorial : ℝ) / (n : ℝ) ^ p := by
  intro r hr hrR
  obtain ⟨L, hL, hσ⟩ := exists_reciprocal_gevrey_parameter hR hr hrR
  have hprofiles (s : ℕ) :=
    polynomial_reciprocal_family_gevrey P s L hC hR hr hL hdegree hsample hσ
  refine ⟨L, hL, hσ, ?_⟩
  intro n p hn hp u hu
  have hs := reciprocal_sampled_summable P n hR hn (hu.trans_lt hrR) hsample
  have hi := reciprocal_complex_remainder_identity P n p u hs.of_norm
    (fun s => ((reciprocalProfile_of_summable P s
      (hprofiles s).1 (hprofiles s).2).1 u hu).2.1)
  obtain ⟨ha, hb⟩ := polynomial_reciprocal_family_remainder_gevrey P L n p
    hC hR hr hL hn hp hdegree hsample hσ
  have hnorm : Summable (fun k : ℕ =>
      ‖(((P (k + 1)).eval (1 / (n : ℝ)) -
        ∑ s ∈ Finset.range p, (P (k + 1)).coeff s * (1 / (n : ℝ)) ^ s : ℝ) : ℂ) *
          u ^ (k + 1)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ha
    intro k
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  refine ⟨hs, hi, ?_⟩
  rw [hi]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (hnorm.tsum_le_tsum (fun k => ?_) ha).trans hb
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  gcongr

end RhAstraSynthesis
