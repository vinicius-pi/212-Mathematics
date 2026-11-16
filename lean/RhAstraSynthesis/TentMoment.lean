import RhAstraSynthesis.DensityCalibration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact Tent Mass and Logarithmic Moment Integral

Evaluates the piecewise integrals `∫ t in 1..2, TentMellin.realTent t` and
`∫ t in 1..2, TentMellin.realTent t * Real.log t`, discharging the hypothesis
`actualMoment = momentPolynomial` in `DensityCalibration` and proving
`0 < calibratedWeight actualMoment < 1`.
-/

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace TentMoment

lemma left_tent (t : ℝ) (ht : t ∈ Icc 1 (4 / 3 : ℝ)) :
    TentMellin.realTent t = 4 * (1 - t⁻¹) := by
  simp [TentMellin.realTent, ht]

lemma right_tent (t : ℝ) (ht : t ∈ Icc (4 / 3 : ℝ) 2) :
    TentMellin.realTent t = 4 / t - 2 := by
  by_cases hc : t = (4 / 3 : ℝ)
  · subst t
    norm_num [TentMellin.realTent]
  · have hleft : t ∉ Icc 1 (4 / 3 : ℝ) := by
      intro h
      exact hc (le_antisymm h.2 ht.1)
    simp [TentMellin.realTent, hleft, ht]

lemma left_weight (f : ℝ → ℝ) (t : ℝ) (ht : t ∈ Icc 1 (4 / 3 : ℝ)) :
    TentMellin.realTent t * f t = 4 * f t - 4 * (f t / t) := by
  rw [left_tent t ht]
  ring

lemma right_weight (f : ℝ → ℝ) (t : ℝ) (ht : t ∈ Icc (4 / 3 : ℝ) 2) :
    TentMellin.realTent t * f t = 4 * (f t / t) - 2 * f t := by
  rw [right_tent t ht]
  ring

theorem weighted_integral_split (f : ℝ → ℝ)
    (hL : IntervalIntegrable f volume 1 (4 / 3 : ℝ))
    (hLD : IntervalIntegrable (fun t => f t / t) volume 1 (4 / 3 : ℝ))
    (hR : IntervalIntegrable f volume (4 / 3 : ℝ) 2)
    (hRD : IntervalIntegrable (fun t => f t / t) volume (4 / 3 : ℝ) 2) :
    (∫ t : ℝ in 1..2, TentMellin.realTent t * f t) =
      4 * (∫ t : ℝ in 1..(4 / 3 : ℝ), f t) -
      4 * (∫ t : ℝ in 1..(4 / 3 : ℝ), f t / t) +
      (4 * (∫ t : ℝ in (4 / 3 : ℝ)..2, f t / t) -
       2 * (∫ t : ℝ in (4 / 3 : ℝ)..2, f t)) := by
  have hl : IntervalIntegrable (fun t => TentMellin.realTent t * f t)
      volume 1 (4 / 3 : ℝ) := by
    apply ((hL.const_mul 4).sub (hLD.const_mul 4)).congr
    intro t ht
    rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 4 / 3)] at ht
    exact (left_weight f t ⟨ht.1.le, ht.2⟩).symm
  have hr : IntervalIntegrable (fun t => TentMellin.realTent t * f t)
      volume (4 / 3 : ℝ) 2 := by
    apply ((hRD.const_mul 4).sub (hR.const_mul 2)).congr
    intro t ht
    rw [uIoc_of_le (by norm_num : (4 / 3 : ℝ) ≤ 2)] at ht
    exact (right_weight f t ⟨ht.1.le, ht.2⟩).symm
  have eL : (∫ t : ℝ in 1..(4 / 3 : ℝ), TentMellin.realTent t * f t) =
      ∫ t : ℝ in 1..(4 / 3 : ℝ), 4 * f t - 4 * (f t / t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4 / 3)] at ht
    exact left_weight f t ht
  have eR : (∫ t : ℝ in (4 / 3 : ℝ)..2, TentMellin.realTent t * f t) =
      ∫ t : ℝ in (4 / 3 : ℝ)..2, 4 * (f t / t) - 2 * f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (4 / 3 : ℝ) ≤ 2)] at ht
    exact right_weight f t ht
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr, eL, eR,
    intervalIntegral.integral_sub (hL.const_mul 4) (hLD.const_mul 4),
    intervalIntegral.integral_sub (hRD.const_mul 4) (hR.const_mul 2)]
  simp only [intervalIntegral.integral_const_mul]

lemma positive_not_zero {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht : t ∈ uIcc a b) : t ≠ 0 := by
  rw [uIcc_of_le hab] at ht
  exact ne_of_gt (lt_of_lt_of_le ha ht.1)

lemma quotient_integrable (f : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (uIcc a b)) :
    IntervalIntegrable (fun t => f t / t) volume a b := by
  exact (hf.div continuousOn_id (fun t ht => positive_not_zero ha hab ht)).intervalIntegrable

lemma log_quotient_integrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Real.log t / t) volume a b := by
  apply quotient_integrable Real.log a b ha hab
  intro t ht
  exact (Real.continuousAt_log (positive_not_zero ha hab ht)).continuousWithinAt

theorem integral_log_quotient (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.log t / t) =
      (Real.log b ^ 2 - Real.log a ^ 2) / 2 := by
  have hd : ∀ t ∈ uIcc a b,
      HasDerivAt (fun x : ℝ => Real.log x ^ 2 / 2) (Real.log t / t) t := by
    intro t ht
    have h := ((Real.hasDerivAt_log (positive_not_zero ha hab ht)).pow 2).div_const (2 : ℝ)
    convert h using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (log_quotient_integrable a b ha hab)
  calc
    _ = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := h
    _ = _ := by ring

theorem actualMoment_eq_polynomial :
    DensityCalibration.actualMoment = DensityCalibration.momentPolynomial := by
  unfold DensityCalibration.actualMoment
  rw [weighted_integral_split Real.log
    intervalIntegral.intervalIntegrable_log'
    (log_quotient_integrable 1 (4 / 3) (by norm_num) (by norm_num))
    intervalIntegral.intervalIntegrable_log'
    (log_quotient_integrable (4 / 3) 2 (by norm_num) (by norm_num))]
  rw [integral_log, integral_log,
    integral_log_quotient 1 (4 / 3) (by norm_num) (by norm_num),
    integral_log_quotient (4 / 3) 2 (by norm_num) (by norm_num)]
  norm_num [DensityCalibration.momentPolynomial, DensityCalibration.logA,
    DensityCalibration.logB]
  ring

theorem actual_tent_mass :
    (∫ t : ℝ in 1..2, TentMellin.realTent t) = DensityCalibration.mass := by
  have hl : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume 1 (4 / 3 : ℝ) :=
    quotient_integrable (fun _ => 1) 1 (4 / 3) (by norm_num) (by norm_num) continuousOn_const
  have hr : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume (4 / 3 : ℝ) 2 :=
    quotient_integrable (fun _ => 1) (4 / 3) 2 (by norm_num) (by norm_num) continuousOn_const
  have h := weighted_integral_split (fun _ : ℝ => (1 : ℝ))
    intervalIntegrable_const hl intervalIntegrable_const hr
  simp only [mul_one] at h
  rw [h, integral_one, integral_one,
    integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 4 / 3),
    integral_one_div_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
      (by norm_num : (0 : ℝ) < 2),
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (4 / 3 : ℝ) ≠ 0),
    DensityCalibration.mass_eq_linear]
  norm_num [DensityCalibration.logA, DensityCalibration.logB]
  ring

theorem actual_calibration :
    0 < DensityCalibration.calibratedWeight DensityCalibration.actualMoment ∧
      DensityCalibration.calibratedWeight DensityCalibration.actualMoment < 1 := by
  have h := DensityCalibration.actual_calibration_of_moment_identity actualMoment_eq_polynomial
  exact ⟨h.2.2.1, h.2.2.2⟩

end TentMoment

