import RhAstraSynthesis.TentMellin
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rational Moment Calibration for the Tent Kernel

Establishes certified rational interval bounds on `log (4 / 3)`, `log 2`,
the tent mass `4 * log (9 / 8)`, and the logarithmic moment polynomial
`momentPolynomial / mass ∈ (3 / 10, 17 / 50)`, yielding well-calibrated mixture
weights in `(0, 1)` against the Euler–Mascheroni constant `γ`.
-/

noncomputable section

open MeasureTheory

namespace DensityCalibration

def logA : ℝ := Real.log (4 / 3)
def logB : ℝ := Real.log 2
def mass : ℝ := 4 * Real.log (9 / 8)

def actualMoment : ℝ :=
  ∫ t : ℝ in (1 : ℝ)..2, TentMellin.realTent t * Real.log t

def momentPolynomial : ℝ :=
  8 * logA - 4 * logB - 4 * logA ^ 2 + 2 * logB ^ 2

def meanLog (u : ℝ) : ℝ := (u * Real.log u - u + 1) / (u - 1)

def centeredMoment (J : ℝ) : ℝ := Real.eulerMascheroniConstant - J / mass

def calibratedWeight (J : ℝ) : ℝ :=
  (meanLog 2 - centeredMoment J) / (meanLog 2 - meanLog (4 / 3))

lemma logA_eq : logA = 2 * logB - Real.log 3 := by
  dsimp only [logA, logB]
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_four_eq]

lemma mass_eq_linear : mass = 4 * logB - 8 * logA := by
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    have h := Real.log_pow (3 : ℝ) 2
    norm_num at h
    exact h
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  dsimp only [mass]
  rw [Real.log_div (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0),
    h9, h8, logA_eq]
  dsimp only [logB]
  ring

lemma mass_pos : 0 < mass := by
  exact mul_pos (by norm_num : (0 : ℝ) < 4)
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8))

/-- Exact rational numeral bounds for `log (4 / 3)` and `log 2`. -/
lemma coarse_log_bounds :
    (28768 / 100000 : ℝ) < logA ∧ logA < 28769 / 100000 ∧
    (69314 / 100000 : ℝ) < logB ∧ logB < 69315 / 100000 := by
  have hbL : (0.6931471803 : ℝ) < logB := Real.log_two_gt_d9
  have hbU : logB < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hcL := Real.log_three_gt_d9
  have hcU := Real.log_three_lt_d9
  have ha := logA_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [ha, hbL, hcU]
  · linarith only [ha, hbU, hcL]
  · linarith only [hbL]
  · linarith only [hbU]

theorem polynomial_ratio_bounds :
    (3 / 10 : ℝ) < momentPolynomial / mass ∧
      momentPolynomial / mass < 17 / 50 := by
  rcases coarse_log_bounds with ⟨haL, haU, hbL, hbU⟩
  have ha0 : 0 ≤ logA := by linarith only [haL]
  have hb0 : 0 ≤ logB := by linarith only [hbL]
  have ha2L : (28768 / 100000 : ℝ) ^ 2 < logA ^ 2 :=
    (sq_lt_sq₀ (by norm_num) ha0).2 haL
  have ha2U : logA ^ 2 < (28769 / 100000 : ℝ) ^ 2 :=
    (sq_lt_sq₀ ha0 (by norm_num)).2 haU
  have hb2L : (69314 / 100000 : ℝ) ^ 2 < logB ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hb0).2 hbL
  have hb2U : logB ^ 2 < (69315 / 100000 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hb0 (by norm_num)).2 hbU
  have hL : (3 / 10 : ℝ) * mass < momentPolynomial := by
    rw [mass_eq_linear]
    dsimp only [momentPolynomial]
    nlinarith only [haL, haU, hbL, hbU, ha2U, hb2L]
  have hU : momentPolynomial < (17 / 50 : ℝ) * mass := by
    rw [mass_eq_linear]
    dsimp only [momentPolynomial]
    nlinarith only [haL, haU, hbL, hbU, ha2L, hb2U]
  exact ⟨(lt_div_iff₀ mass_pos).2 hL, (div_lt_iff₀ mass_pos).2 hU⟩

lemma meanLog_four_thirds : meanLog (4 / 3) = 4 * logA - 1 := by
  unfold meanLog logA
  ring

lemma meanLog_two : meanLog 2 = 2 * logB - 1 := by
  unfold meanLog logB
  ring

lemma meanLog_gap : meanLog 2 - meanLog (4 / 3) = mass / 2 := by
  rw [meanLog_two, meanLog_four_thirds, mass_eq_linear]
  ring

lemma meanLog_gap_pos : 0 < meanLog 2 - meanLog (4 / 3) := by
  rw [meanLog_gap]
  exact div_pos mass_pos (by norm_num)

theorem coarse_mean_bounds :
    meanLog (4 / 3) < (4 / 25 : ℝ) ∧ (19 / 50 : ℝ) < meanLog 2 := by
  rcases coarse_log_bounds with ⟨haL, haU, hbL, hbU⟩
  rw [meanLog_four_thirds, meanLog_two]
  constructor
  · linarith only [haU]
  · linarith only [hbL]

lemma centeredMoment_bounds_of_ratio (J : ℝ)
    (hL : (3 / 10 : ℝ) < J / mass) (hU : J / mass < (17 / 50 : ℝ)) :
    (4 / 25 : ℝ) < centeredMoment J ∧ centeredMoment J < (11 / 30 : ℝ) := by
  have hgL := Real.one_half_lt_eulerMascheroniConstant
  have hgU := Real.eulerMascheroniConstant_lt_two_thirds
  dsimp only [centeredMoment]
  constructor
  · linarith only [hgL, hU]
  · linarith only [hgU, hL]

theorem calibratedWeight_bounds_of_ratio (J : ℝ)
    (hL : (3 / 10 : ℝ) < J / mass) (hU : J / mass < (17 / 50 : ℝ)) :
    0 < calibratedWeight J ∧ calibratedWeight J < 1 := by
  obtain ⟨hzL, hzU⟩ := centeredMoment_bounds_of_ratio J hL hU
  obtain ⟨hmL, hmU⟩ := coarse_mean_bounds
  have hz1 : meanLog (4 / 3) < centeredMoment J := hmL.trans hzL
  have hz2 : centeredMoment J < meanLog 2 := by linarith only [hzU, hmU]
  dsimp only [calibratedWeight]
  constructor
  · exact div_pos (sub_pos.mpr hz2) meanLog_gap_pos
  · apply (div_lt_one meanLog_gap_pos).2
    linarith only [hz1]

/-- Exact linear convex combination identity for `calibratedWeight J`. -/
theorem calibrated_mean (J : ℝ) :
    calibratedWeight J * meanLog (4 / 3) +
      (1 - calibratedWeight J) * meanLog 2 = centeredMoment J := by
  have hden : meanLog 2 - meanLog (4 / 3) ≠ 0 := ne_of_gt meanLog_gap_pos
  dsimp only [calibratedWeight]
  field_simp [hden]
  ring

/-- Conditional interface connecting `actualMoment = momentPolynomial` to `(0, 1)` weight bounds. -/
theorem actual_calibration_of_moment_identity
    (hJ : actualMoment = momentPolynomial) :
    (3 / 10 : ℝ) < actualMoment / mass ∧
    actualMoment / mass < (17 / 50 : ℝ) ∧
    0 < calibratedWeight actualMoment ∧ calibratedWeight actualMoment < 1 := by
  have hratio := polynomial_ratio_bounds
  rw [← hJ] at hratio
  have hweight := calibratedWeight_bounds_of_ratio actualMoment hratio.1 hratio.2
  exact ⟨hratio.1, hratio.2, hweight.1, hweight.2⟩

end DensityCalibration

