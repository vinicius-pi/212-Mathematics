import RhAstraSynthesis.PrimePowerMellin
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mellin Transform of the Ramp-Weighted Uniform Density

Formalizes the uniform probability law on `[1, b]` (`1 < b`), its weighted CDF
density `y * rampCDF b y`, Mellin convergence on `Re(s) > 1`, and the exact
Mellin identity `HasMellin (density b) (-s) ((∫ y in 1..b, y^(1-s)) / ((b-1)*(s-1)))`.
-/

noncomputable section
open Set MeasureTheory
open scoped Interval ENNReal

namespace TentDensity

def rampCDF (b y : ℝ) : ℝ :=
  if y ≤ 1 then 0 else if y ≤ b then (y - 1) / (b - 1) else 1

def uniformLaw (b : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (1 : ℝ) b)

theorem uniformLaw_probability (b : ℝ) (hb : 1 < b) :
    IsProbabilityMeasure (uniformLaw b) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hb))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem uniformLaw_interval (b : ℝ) (hb : 1 < b) (y : ℝ) :
    ((uniformLaw b) (Icc (1 : ℝ) y)).toReal = rampCDF b y := by
  unfold uniformLaw
  rw [ProbabilityTheory.cond_apply (s := Icc (1 : ℝ) b)
      measurableSet_Icc volume (Icc (1 : ℝ) y),
    Icc_inter_Icc, max_self, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hb.le), ENNReal.toReal_ofReal']
  by_cases hy : y ≤ 1
  · simp [rampCDF, hy]
  · by_cases hyb : y ≤ b
    · simp [rampCDF, hy, hyb,
        max_eq_left (sub_nonneg.mpr (le_of_not_ge hy)),
        div_eq_mul_inv, mul_comm]
    · simp [rampCDF, hy, hyb, min_eq_left (le_of_not_ge hyb),
        max_eq_left (sub_nonneg.mpr hb.le), (sub_pos.mpr hb).ne']

def density (b y : ℝ) : ℂ := ((y * rampCDF b y : ℝ) : ℂ)

def densityPieces (b y : ℝ) : ℂ :=
  (Ioc (1 : ℝ) b).indicator
      (fun t : ℝ => (t : ℂ) * ((t : ℂ) - 1) / ((b : ℂ) - 1)) y +
    (Ioi b).indicator (fun t : ℝ => (t : ℂ)) y

theorem density_eq_pieces (b : ℝ) (hb : 1 < b) (y : ℝ) :
    density b y = densityPieces b y := by
  classical
  by_cases hy : y ≤ 1
  · have hi : y ∉ Ioc (1 : ℝ) b := fun h => (not_lt_of_ge hy) h.1
    have ht : y ∉ Ioi b := by
      intro h
      linarith [mem_Ioi.mp h]
    simp [density, rampCDF, densityPieces, hy, hi, ht]
  · by_cases hyb : y ≤ b
    · have hi : y ∈ Ioc (1 : ℝ) b := ⟨lt_of_not_ge hy, hyb⟩
      have ht : y ∉ Ioi b := not_lt_of_ge hyb
      simp [density, rampCDF, densityPieces, hy, hyb, hi, ht, div_eq_mul_inv,
        mul_assoc]
    · have hi : y ∉ Ioc (1 : ℝ) b := fun h => hyb h.2
      have ht : y ∈ Ioi b := lt_of_not_ge hyb
      simp [density, rampCDF, densityPieces, hy, hyb, hi, ht]

lemma cpow_mul_base (y : ℝ) (hy : 0 < y) (z : ℂ) :
    (y : ℂ) ^ z * (y : ℂ) = (y : ℂ) ^ (z + 1) := by
  simpa only [Complex.cpow_one] using
    (Complex.cpow_add z (1 : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne')).symm

lemma tail_weight (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (-s - 1) * (y : ℂ) = (y : ℂ) ^ (-s) := by
  simpa only [sub_add_cancel] using cpow_mul_base y hy (-s - 1)

lemma interval_weight (b : ℝ) (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (-s - 1) *
      ((y : ℂ) * ((y : ℂ) - 1) / ((b : ℂ) - 1)) =
      ((y : ℂ) ^ (1 - s) - (y : ℂ) ^ (-s)) / ((b : ℂ) - 1) := by
  have hp : (y : ℂ) ^ (-s) * (y : ℂ) = (y : ℂ) ^ (1 - s) := by
    simpa only [show -s + 1 = 1 - s by ring] using cpow_mul_base y hy (-s)
  calc
    _ = ((y : ℂ) ^ (-s - 1) * (y : ℂ) * (y : ℂ) -
      (y : ℂ) ^ (-s - 1) * (y : ℂ)) / ((b : ℂ) - 1) := by ring
    _ = _ := by rw [tail_weight s y hy, hp]

lemma interval_weight_integrable (b : ℝ) (hb : 1 < b) (s : ℂ) :
    IntervalIntegrable
      (fun y : ℝ => (y : ℂ) ^ (-s - 1) *
        ((y : ℂ) * ((y : ℂ) - 1) / ((b : ℂ) - 1))) volume 1 b := by
  have h1 := TentMellin.power_integrable 1 b (by norm_num) hb.le (1 - s)
  have h0 := TentMellin.power_integrable 1 b (by norm_num) hb.le (-s)
  apply ((h1.sub h0).div_const ((b : ℂ) - 1)).congr
  intro y hy
  rw [uIoc_of_le hb.le] at hy
  exact (interval_weight b s y (by linarith [hy.1])).symm

lemma interval_piece_convergent (b : ℝ) (hb : 1 < b) (s : ℂ) :
    MellinConvergent
      ((Ioc (1 : ℝ) b).indicator
        (fun y : ℝ => (y : ℂ) * ((y : ℂ) - 1) / ((b : ℂ) - 1))) (-s) :=
  TentMellin.convergent_indicator_Ioc 1 b _ (-s) (interval_weight_integrable b hb s)

lemma tail_piece_convergent (b : ℝ) (hb : 1 < b) (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent ((Ioi b).indicator (fun y : ℝ => (y : ℂ))) (-s) := by
  have hp := integrableOn_Ioi_cpow_of_lt
    (show (-s).re < -1 by simp only [Complex.neg_re]; linarith)
    (show 0 < b by linarith)
  have hw : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (-s - 1) * (y : ℂ)) (Ioi b) := by
    apply hp.congr_fun _ measurableSet_Ioi
    intro y hy
    exact (tail_weight s y (by linarith [mem_Ioi.mp hy])).symm
  unfold MellinConvergent
  rw [TentMellin.weighted_indicator]
  exact (hw.integrable_indicator measurableSet_Ioi).integrableOn

theorem density_mellin_convergent (b : ℝ) (hb : 1 < b) (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent (density b) (-s) := by
  have he : density b = densityPieces b := funext (density_eq_pieces b hb)
  rw [he]
  exact (hasMellin_add (interval_piece_convergent b hb s)
    (tail_piece_convergent b hb s hs)).1

lemma mellin_indicator_Ioi (b : ℝ) (hb : 0 ≤ b) (f : ℝ → ℂ) (s : ℂ) :
    mellin ((Ioi b).indicator f) s =
      ∫ y : ℝ in Ioi b, (y : ℂ) ^ (s - 1) * f y := by
  have hsub : Ioi b ⊆ Ioi (0 : ℝ) := fun _ hy => lt_of_le_of_lt hb hy
  unfold mellin
  rw [TentMellin.weighted_indicator, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset hsub]

lemma density_mellin_split (b : ℝ) (hb : 1 < b) (s : ℂ) (hs : 1 < s.re) :
    mellin (density b) (-s) =
      ((∫ y : ℝ in 1..b, (y : ℂ) ^ (1 - s)) -
        (∫ y : ℝ in 1..b, (y : ℂ) ^ (-s))) / ((b : ℂ) - 1) +
      ∫ y : ℝ in Ioi b, (y : ℂ) ^ (-s) := by
  have he : density b = densityPieces b := funext (density_eq_pieces b hb)
  rw [he]
  change mellin (fun y => _ + _) (-s) = _
  rw [(hasMellin_add (interval_piece_convergent b hb s)
    (tail_piece_convergent b hb s hs)).2,
    TentMellin.mellin_indicator_Ioc 1 b (by norm_num) hb.le,
    mellin_indicator_Ioi b (by linarith)]
  congr 1
  · calc
      _ = ∫ y : ℝ in 1..b,
          ((y : ℂ) ^ (1 - s) - (y : ℂ) ^ (-s)) / ((b : ℂ) - 1) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hb.le] at hy
        exact interval_weight b s y (by linarith [hy.1])
      _ = _ := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
          (TentMellin.power_integrable 1 b (by norm_num) hb.le (1 - s))
          (TentMellin.power_integrable 1 b (by norm_num) hb.le (-s))]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact tail_weight s y (by linarith [mem_Ioi.mp hy])

lemma moment_relation (b : ℝ) (hb : 1 < b) (s : ℂ) :
    (2 - s) * (∫ y : ℝ in 1..b, (y : ℂ) ^ (1 - s)) =
      (b : ℂ) ^ (2 - s) - 1 := by
  have hd : ∀ y ∈ uIcc (1 : ℝ) b,
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (2 - s))
        ((2 - s) * (y : ℂ) ^ (1 - s)) y := by
    intro y hy
    rw [uIcc_of_le hb.le] at hy
    have hslit : (y : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.mpr (by linarith [hy.1])
    simpa only [show 2 - s - 1 = 1 - s by ring] using
      (Complex.hasStrictDerivAt_cpow_const (c := 2 - s) hslit).hasDerivAt.comp_ofReal
  have hp := TentMellin.power_integrable 1 b (by norm_num) hb.le (1 - s)
  simpa only [intervalIntegral.integral_const_mul, Complex.ofReal_one, Complex.one_cpow] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hp.const_mul (2 - s))

theorem density_hasMellin (b : ℝ) (hb : 1 < b) (s : ℂ) (hs : 1 < s.re) :
    HasMellin (density b) (-s)
      ((∫ y : ℝ in 1..b, (y : ℂ) ^ (1 - s)) / (((b : ℂ) - 1) * (s - 1))) := by
  refine ⟨density_mellin_convergent b hb s hs, ?_⟩
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  have hs10 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hbs : (b : ℂ) - 1 ≠ 0 := by exact_mod_cast (sub_pos.mpr hb).ne'
  have hc : (∫ y : ℝ in 1..b, (y : ℂ) ^ (-s)) =
      ((b : ℂ) ^ (1 - s) - 1) / (1 - s) := by
    simpa only [show (1 - s) - 1 = -s by ring, Complex.ofReal_one, Complex.one_cpow] using
      TentMellin.integral_shift_one 1 b (by norm_num) hb.le (1 - s) hs10
  have ht : (∫ y : ℝ in Ioi b, (y : ℂ) ^ (-s)) =
      (b : ℂ) ^ (1 - s) / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith : (-s).re < -1)
      (by linarith : 0 < b)]
    rw [show (-s + 1 : ℂ) = 1 - s by ring]
    field_simp [hs10, hs1']
    ring
  have hbp : (b : ℂ) ^ (1 - s) * (b : ℂ) = (b : ℂ) ^ (2 - s) := by
    simpa only [show (1 - s) + 1 = 2 - s by ring] using
      cpow_mul_base b (by linarith) (1 - s)
  rw [density_mellin_split b hb s hs, hc, ht]
  calc
    _ = ((∫ y : ℝ in 1..b, (y : ℂ) ^ (1 - s)) +
        ((b : ℂ) ^ (2 - s) - 1) / (s - 1)) / ((b : ℂ) - 1) := by
      rw [← hbp]
      field_simp [hbs, hs10, hs1']
      ring
    _ = _ := by
      rw [← moment_relation b hb s]
      field_simp [hbs, hs1']
      ring

end TentDensity

