import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-!
# Power decay through the floor kernel

Explicit Lebesgue-integral error bounds for the normalized floor-kernel transform
`kernel G K = K⁻¹ * ∫_{1}^{K} ⌊K/t⌋ G(t) dt` relative to `∫_{1}^{∞} G(t)/t dt`
under power decay `|G(t)| ≤ C t^(-γ)` (`0 < γ < 1`), together with the two-exponent
minimax balance `80 / 89` at `a = 53 / 89`.
-/

open MeasureTheory Set Filter
open scoped Interval

namespace PowerKernelTransfer

/-- The tail of a power-bounded function divided by its variable. -/
theorem tail_bound {G : ℝ → ℝ} {C γ K : ℝ} (_hC : 0 ≤ C) (hγ : 0 < γ)
    (hK : 1 ≤ K) (hG : ∀ t, 1 ≤ t → |G t| ≤ C * t ^ (-γ)) :
    |∫ t in Ioi K, G t / t| ≤ C / γ * K ^ (-γ) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hp : -γ - 1 < -1 := by linarith
  have hint := (integrableOn_Ioi_rpow_of_lt hp hKpos).const_mul C
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioi K), ‖G t / t‖ ≤ C * t ^ (-γ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := hK.trans (le_of_lt ht)
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
    calc
      |G t| / t ≤ (C * t ^ (-γ)) / t := div_le_div_of_nonneg_right (hG t ht1) htpos.le
      _ = C * t ^ (-γ - 1) := by rw [Real.rpow_sub htpos, Real.rpow_one]; ring
  have h := MeasureTheory.norm_integral_le_of_norm_le hint hnorm
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt hp hKpos] at h
  rw [show -γ - 1 + 1 = -γ by ring] at h
  calc
    |∫ t in Ioi K, G t / t| ≤ C * (-K ^ (-γ) / -γ) := h
    _ = C / γ * K ^ (-γ) := by ring

/-- The fractional-part term has an explicit integral majorant. -/
theorem fractional_integral_bound {G : ℝ → ℝ} {C γ K : ℝ} (hC : 0 ≤ C)
    (hγ : γ < 1) (hK : 1 ≤ K)
    (hG : ∀ t, 1 ≤ t → |G t| ≤ C * t ^ (-γ)) :
    |∫ t in (1 : ℝ)..K, Int.fract (K / t) * G t| ≤
      C / (1 - γ) * K ^ (1 - γ) := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ C * t ^ (-γ)) volume 1 K :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -γ)).const_mul C
  have hnorm : ∀ᵐ t ∂volume, t ∈ Ioc (1 : ℝ) K →
      ‖Int.fract (K / t) * G t‖ ≤ C * t ^ (-γ) := by
    exact Eventually.of_forall fun t ht ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
      calc
        Int.fract (K / t) * |G t| ≤ 1 * |G t| :=
          mul_le_mul_of_nonneg_right (Int.fract_lt_one _).le (abs_nonneg _)
        _ ≤ C * t ^ (-γ) := by simpa using hG t ht.1.le
  have h := intervalIntegral.norm_integral_le_of_norm_le hK hnorm hint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < -γ))] at h
  have hc : 0 ≤ C / (1 - γ) := div_nonneg hC (by linarith)
  have hone : (1 : ℝ) ^ (-γ + 1) = 1 := by simp
  rw [hone] at h
  calc
    |∫ t in (1 : ℝ)..K, Int.fract (K / t) * G t| ≤
        C * ((K ^ (-γ + 1) - 1) / (-γ + 1)) := h
    _ = C / (1 - γ) * (K ^ (1 - γ) - 1) := by
      rw [show -γ + 1 = 1 - γ by ring]
      ring
    _ ≤ C / (1 - γ) * K ^ (1 - γ) := mul_le_mul_of_nonneg_left (by linarith) hc

/-- The exact two terms that occur in the floor-kernel error. -/
noncomputable def remainder (G : ℝ → ℝ) (K : ℝ) : ℝ :=
  -(∫ t in Ioi K, G t / t) - K⁻¹ * (∫ t in (1 : ℝ)..K, Int.fract (K / t) * G t)

/-- Both the improper tail and the fractional term retain the power exponent. -/
theorem remainder_bound {G : ℝ → ℝ} {C γ K : ℝ} (hC : 0 ≤ C)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hK : 1 ≤ K)
    (hG : ∀ t, 1 ≤ t → |G t| ≤ C * t ^ (-γ)) :
    |remainder G K| ≤ C * (1 / γ + 1 / (1 - γ)) * K ^ (-γ) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have ht := tail_bound hC hγ0 hK hG
  have hf := fractional_integral_bound hC hγ1 hK hG
  calc
    |remainder G K| ≤ |∫ t in Ioi K, G t / t| +
        K⁻¹ * |∫ t in (1 : ℝ)..K, Int.fract (K / t) * G t| := by
      unfold remainder
      simpa [abs_mul, abs_of_pos (inv_pos.mpr hKpos)] using
        abs_sub (-(∫ t in Ioi K, G t / t))
          (K⁻¹ * (∫ t in (1 : ℝ)..K, Int.fract (K / t) * G t))
    _ ≤ C / γ * K ^ (-γ) + K⁻¹ * (C / (1 - γ) * K ^ (1 - γ)) :=
      add_le_add ht (mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hKpos.le))
    _ = C * (1 / γ + 1 / (1 - γ)) * K ^ (-γ) := by
      have hp : K ^ (1 - γ) = K ^ (-γ) * K := by
        rw [show 1 - γ = -γ + 1 by ring, Real.rpow_add hKpos, Real.rpow_one]
      rw [hp]
      field_simp

/-- Measurability plus the stated decay supplies actual integrability of the tail. -/
theorem weighted_integrable {G : ℝ → ℝ} {C γ K : ℝ} (hGm : Measurable G)
    (hγ : 0 < γ) (hK : 1 ≤ K)
    (hG : ∀ t, 1 ≤ t → |G t| ≤ C * t ^ (-γ)) :
    IntegrableOn (fun t ↦ G t / t) (Ioi K) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hint := (integrableOn_Ioi_rpow_of_lt (by linarith : -γ - 1 < -1) hKpos).const_mul C
  apply hint.mono' ((hGm.div measurable_id).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := hK.trans ht.le
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  change ‖G t / t‖ ≤ C * t ^ (-γ - 1)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
  calc
    |G t| / t ≤ (C * t ^ (-γ)) / t := div_le_div_of_nonneg_right (hG t ht1) htpos.le
    _ = C * t ^ (-γ - 1) := by rw [Real.rpow_sub htpos, Real.rpow_one]; ring

/-- The normalized floor integral. -/
noncomputable def kernel (G : ℝ → ℝ) (K : ℝ) : ℝ :=
  K⁻¹ * (∫ t in (1 : ℝ)..K, (⌊K / t⌋ : ℝ) * G t)

noncomputable def limitIntegral (G : ℝ → ℝ) : ℝ := ∫ t in Ioi (1 : ℝ), G t / t

/-- Exact identity, including integrability: the floor-kernel error is the remainder. -/
theorem kernel_sub_limit {G : ℝ → ℝ} {C γ K : ℝ} (hGm : Measurable G)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hK : 1 ≤ K)
    (hG : ∀ t, 1 ≤ t → |G t| ≤ C * t ^ (-γ)) :
    kernel G K - limitIntegral G = remainder G K := by
  have hi1 := weighted_integrable hGm hγ0 (le_refl (1 : ℝ)) hG
  have hiK := weighted_integrable hGm hγ0 hK hG
  have hqi : IntervalIntegrable (fun t ↦ G t / t) volume 1 K :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hK).2
      (hi1.mono_set Ioc_subset_Ioi_self)
  have hfi : IntervalIntegrable (fun t ↦ Int.fract (K / t) * G t) volume 1 K := by
    have hp : IntervalIntegrable (fun t : ℝ ↦ C * t ^ (-γ)) volume 1 K :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -γ)).const_mul C
    apply hp.mono_fun' ((measurable_fract.comp (measurable_const.div measurable_id)).mul hGm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hK] at ht
    change ‖Int.fract (K / t) * G t‖ ≤ C * t ^ (-γ)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
    calc
      Int.fract (K / t) * |G t| ≤ 1 * |G t| :=
        mul_le_mul_of_nonneg_right (Int.fract_lt_one _).le (abs_nonneg _)
      _ ≤ C * t ^ (-γ) := by simpa using hG t ht.1.le
  have heq : (∫ t in (1 : ℝ)..K, (⌊K / t⌋ : ℝ) * G t) =
      K * (∫ t in (1 : ℝ)..K, G t / t) -
        (∫ t in (1 : ℝ)..K, Int.fract (K / t) * G t) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hqi.const_mul K) hfi]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hK] at ht
    have htne : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    have hfloor := Int.floor_add_fract (K / t)
    have hprod := congrArg (fun x : ℝ ↦ x * G t) hfloor
    field_simp at hprod ⊢
    nlinarith
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi1 hiK
  unfold kernel limitIntegral remainder
  rw [heq, ← hsplit]
  have hKne : K ≠ 0 := ne_of_gt (zero_lt_one.trans_le hK)
  field_simp
  ring

/-- Certified analytic implication from explicit measurable power decay to kernel decay. -/
theorem kernel_error_bound {G : ℝ → ℝ} {C γ K : ℝ} (hGm : Measurable G)
    (hC : 0 ≤ C) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hK : 1 ≤ K)
    (hG : ∀ t, 1 ≤ t → |G t| ≤ C * t ^ (-γ)) :
    |kernel G K - limitIntegral G| ≤ C * (1 / γ + 1 / (1 - γ)) * K ^ (-γ) := by
  rw [kernel_sub_limit hGm hγ0 hγ1 hK hG]
  exact remainder_bound hC hγ0 hγ1 hK hG

/-- Minimax balance across the two error exponents `(3 + a) / 4` and `(26 - 18a) / 17`. -/
theorem exponent_envelope (a : ℝ) :
    (80 : ℝ) / 89 ≤ max ((3 + a) / 4) ((26 - 18 * a) / 17) := by
  by_cases ha : (53 : ℝ) / 89 ≤ a
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact le_trans (by linarith) (le_max_right _ _)

end PowerKernelTransfer
