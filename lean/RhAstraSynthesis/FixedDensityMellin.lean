import RhAstraSynthesis.TentMoment
import RhAstraSynthesis.DensityMellin

/-!
# Centered Prime-Power Density Mellin Identity

Constructs the calibrated convex mixture `mixtureLaw` of uniform laws on
`[1, 4/3]` and `[1, 2]`, evaluates the Mellin transform of the weighted
distribution `actualDensity`, and proves `centeredPrimePower_hasMellin_measure`
relating the centered prime-power remainder to `mellin tent s * (-ζ'(s)/ζ(s))`.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal Interval

namespace FixedDensityMellin

def weight : ℝ :=
  DensityCalibration.calibratedWeight DensityCalibration.actualMoment

lemma weight_bounds : 0 < weight ∧ weight < 1 :=
  TentMoment.actual_calibration

def mixtureLaw : Measure ℝ :=
  ENNReal.ofReal weight • TentDensity.uniformLaw (4 / 3) +
  ENNReal.ofReal (1 - weight) • TentDensity.uniformLaw 2

def distribution (y : ℝ) : ℝ := (mixtureLaw (Icc (1 : ℝ) y)).toReal

def actualDensity (y : ℝ) : ℂ :=
  ((DensityCalibration.mass * y * distribution y : ℝ) : ℂ)

theorem mixtureLaw_probability : IsProbabilityMeasure mixtureLaw := by
  let inst43 := TentDensity.uniformLaw_probability (4 / 3) (by norm_num)
  let inst2 := TentDensity.uniformLaw_probability 2 (by norm_num)
  have h0 : 0 ≤ weight := weight_bounds.1.le
  have h1 : 0 ≤ 1 - weight := sub_nonneg.mpr weight_bounds.2.le
  constructor
  simp only [mixtureLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 h1]
  norm_num

theorem distribution_eq (y : ℝ) :
    distribution y =
      weight * TentDensity.rampCDF (4 / 3) y +
      (1 - weight) * TentDensity.rampCDF 2 y := by
  let inst43 := TentDensity.uniformLaw_probability (4 / 3) (by norm_num)
  let inst2 := TentDensity.uniformLaw_probability 2 (by norm_num)
  have hf1 : ENNReal.ofReal weight *
      TentDensity.uniformLaw (4 / 3) (Icc (1 : ℝ) y) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hf2 : ENNReal.ofReal (1 - weight) *
      TentDensity.uniformLaw 2 (Icc (1 : ℝ) y) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  simp only [distribution, mixtureLaw, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [ENNReal.toReal_add hf1 hf2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal weight_bounds.1.le,
    ENNReal.toReal_ofReal (sub_nonneg.mpr weight_bounds.2.le),
    TentDensity.uniformLaw_interval (4 / 3) (by norm_num),
    TentDensity.uniformLaw_interval 2 (by norm_num)]

theorem actualDensity_eq (y : ℝ) :
    actualDensity y = (DensityCalibration.mass : ℂ) *
      ((weight : ℂ) * TentDensity.density (4 / 3) y +
        ((1 - weight : ℝ) : ℂ) * TentDensity.density 2 y) := by
  rw [actualDensity, distribution_eq]
  simp only [TentDensity.density, Complex.ofReal_mul, Complex.ofReal_add]
  ring

def momentFactor (s : ℂ) : ℂ :=
  (weight : ℂ) / (((4 / 3 : ℝ) : ℂ) - 1) *
      (∫ a : ℝ in 1..(4 / 3 : ℝ), (a : ℂ) ^ (1 - s)) +
    ((1 - weight : ℝ) : ℂ) *
      (∫ a : ℝ in 1..2, (a : ℂ) ^ (1 - s))

lemma uniformLaw_integral (b : ℝ) (hb : 1 < b) (f : ℝ → ℂ) :
    (∫ a : ℝ, f a ∂TentDensity.uniformLaw b) =
      (∫ a : ℝ in 1..b, f a) / ((b : ℂ) - 1) := by
  unfold TentDensity.uniformLaw ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hb.le),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le,
    ← Complex.coe_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, smul_eq_mul]
  ring

lemma uniformLaw_cpow_integrable (b : ℝ) (hb : 1 < b) (s : ℂ) :
    Integrable (fun a : ℝ => (a : ℂ) ^ (1 - s)) (TentDensity.uniformLaw b) := by
  have hp : IntegrableOn (fun a : ℝ => (a : ℂ) ^ (1 - s)) (Icc 1 b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).1
      (TentMellin.power_integrable 1 b (by norm_num) hb.le (1 - s))
  have hne : volume (Icc (1 : ℝ) b) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hb))
  unfold TentDensity.uniformLaw ProbabilityTheory.cond
  exact hp.smul_measure (ENNReal.inv_ne_top.mpr hne)

def measureMoment (s : ℂ) : ℂ :=
  ∫ a : ℝ, (a : ℂ) ^ (1 - s) ∂mixtureLaw

theorem momentFactor_eq_measureMoment (s : ℂ) : momentFactor s = measureMoment s := by
  have h1 := (uniformLaw_cpow_integrable (4 / 3) (by norm_num) s).smul_measure
    (c := ENNReal.ofReal weight) ENNReal.ofReal_ne_top
  have h2 := (uniformLaw_cpow_integrable 2 (by norm_num) s).smul_measure
    (c := ENNReal.ofReal (1 - weight)) ENNReal.ofReal_ne_top
  unfold measureMoment mixtureLaw
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal weight_bounds.1.le,
    ENNReal.toReal_ofReal (sub_nonneg.mpr weight_bounds.2.le),
    uniformLaw_integral (4 / 3) (by norm_num), uniformLaw_integral 2 (by norm_num)]
  simp only [← Complex.coe_smul, smul_eq_mul]
  unfold momentFactor
  norm_num
  ring

theorem actualDensity_hasMellin (s : ℂ) (hs : 1 < s.re) :
    HasMellin actualDensity (-s)
      ((DensityCalibration.mass : ℂ) * momentFactor s / (s - 1)) := by
  have h1 := TentDensity.density_hasMellin (4 / 3) (by norm_num) s hs
  have h2 := TentDensity.density_hasMellin 2 (by norm_num) s hs
  have ha := h1.1.const_smul (weight : ℂ)
  have hb := h2.1.const_smul ((1 - weight : ℝ) : ℂ)
  have he : actualDensity = fun y : ℝ =>
      (DensityCalibration.mass : ℂ) •
        ((weight : ℂ) • TentDensity.density (4 / 3) y +
          ((1 - weight : ℝ) : ℂ) • TentDensity.density 2 y) := by
    funext y
    exact actualDensity_eq y
  refine ⟨?_, ?_⟩
  · rw [he]
    exact (hasMellin_add ha hb).1.const_smul (DensityCalibration.mass : ℂ)
  · have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; subst s; norm_num at hs)
    rw [he, mellin_const_smul, (hasMellin_add ha hb).2,
      mellin_const_smul, mellin_const_smul, h1.2, h2.2]
    simp only [smul_eq_mul]
    unfold momentFactor
    norm_num
    field_simp [hs1]

def centeredPrimePower (y : ℝ) : ℂ :=
  PrimePowerMellin.primePower y - actualDensity y

theorem centeredPrimePower_hasMellin (s : ℂ) (hs : 1 < s.re) :
    HasMellin centeredPrimePower (-s)
      (mellin TentMellin.tent s * (-deriv riemannZeta s / riemannZeta s) -
        (DensityCalibration.mass : ℂ) * momentFactor s / (s - 1)) := by
  have hp := PrimePowerMellin.primePower_hasMellin s hs
  have hg := actualDensity_hasMellin s hs
  refine ⟨(hasMellin_sub hp.1 hg.1).1, ?_⟩
  change mellin (fun y : ℝ => PrimePowerMellin.primePower y - actualDensity y) (-s) = _
  rw [(hasMellin_sub hp.1 hg.1).2, hp.2, hg.2]

theorem centeredPrimePower_hasMellin_measure (s : ℂ) (hs : 1 < s.re) :
    HasMellin centeredPrimePower (-s)
      (mellin TentMellin.tent s * (-deriv riemannZeta s / riemannZeta s) -
        (DensityCalibration.mass : ℂ) * measureMoment s / (s - 1)) := by
  simpa only [momentFactor_eq_measureMoment] using centeredPrimePower_hasMellin s hs

end FixedDensityMellin

#print axioms FixedDensityMellin.mixtureLaw_probability
#print axioms FixedDensityMellin.momentFactor_eq_measureMoment
#print axioms FixedDensityMellin.actualDensity_hasMellin
#print axioms FixedDensityMellin.centeredPrimePower_hasMellin
#print axioms FixedDensityMellin.centeredPrimePower_hasMellin_measure
