import RhAstraSynthesis.TentMultiplier
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mellin transform of the supported tent kernel

Proves entire Mellin convergence of the piecewise-smooth tent kernel supported on
`[1, 2]`, evaluates `mellin tent s = TentMultiplier.multiplier s` for `s ≠ 0, 1`,
and deduces non-vanishing on `0 < Re(s) < 1`.
-/

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace TentMellin

def realTent (t : ℝ) : ℝ :=
  if t ∈ Icc 1 (4 / 3 : ℝ) then 4 * (1 - t⁻¹)
  else if t ∈ Icc (4 / 3 : ℝ) 2 then 4 / t - 2 else 0

def tent (t : ℝ) : ℂ :=
  if t ∈ Icc 1 (4 / 3 : ℝ) then 4 * (1 - (t : ℂ)⁻¹)
  else if t ∈ Icc (4 / 3 : ℝ) 2 then 4 / (t : ℂ) - 2 else 0

theorem ofReal_realTent (t : ℝ) : (realTent t : ℂ) = tent t := by
  classical
  by_cases h1 : t ∈ Icc 1 (4 / 3 : ℝ) <;>
    by_cases h2 : t ∈ Icc (4 / 3 : ℝ) 2 <;> simp [realTent, tent, h1, h2]

def pieces (t : ℝ) : ℂ :=
  (Ioc 1 (4 / 3 : ℝ)).indicator (fun x : ℝ => 4 * (1 - (x : ℂ)⁻¹)) t +
  (Ioc (4 / 3 : ℝ) 2).indicator (fun x : ℝ => 4 / (x : ℂ) - 2) t

theorem tent_eq_pieces (t : ℝ) : tent t = pieces t := by
  classical
  by_cases ha : t = 1
  · subst t
    norm_num [tent, pieces, Set.indicator]
  by_cases hb : t = (4 / 3 : ℝ)
  · subst t
    norm_num [tent, pieces, Set.indicator]
  have hI1 : t ∈ Icc 1 (4 / 3 : ℝ) ↔ t ∈ Ioc 1 (4 / 3 : ℝ) := by
    constructor
    · intro h
      exact ⟨lt_of_le_of_ne h.1 (Ne.symm ha), h.2⟩
    · exact fun h => ⟨h.1.le, h.2⟩
  have hI2 : t ∈ Icc (4 / 3 : ℝ) 2 ↔ t ∈ Ioc (4 / 3 : ℝ) 2 := by
    constructor
    · intro h
      exact ⟨lt_of_le_of_ne h.1 (Ne.symm hb), h.2⟩
    · exact fun h => ⟨h.1.le, h.2⟩
  simp only [tent, pieces, hI1, hI2]
  by_cases h1 : t ∈ Ioc 1 (4 / 3 : ℝ)
  · have h2 : t ∉ Ioc (4 / 3 : ℝ) 2 := by
      intro h
      exact (not_lt_of_ge h1.2) h.1
    simp [h1, h2]
  · by_cases h2 : t ∈ Ioc (4 / 3 : ℝ) 2 <;> simp [h1, h2]

lemma zero_not_uIcc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (0 : ℝ) ∉ [[a, b]] := by
  rw [uIcc_of_le hab]
  intro h
  exact (not_le_of_gt ha) h.1

lemma cpow_div_base (t : ℝ) (ht : 0 < t) (s : ℂ) :
    (t : ℂ) ^ (s - 1) / (t : ℂ) = (t : ℂ) ^ (s - 2) := by
  have hz : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : s - 1 = (s - 2) + 1 := by ring
  rw [he, Complex.cpow_add _ _ hz, Complex.cpow_one]
  exact mul_div_cancel_right₀ _ hz

lemma weighted_indicator (A : Set ℝ) (f : ℝ → ℂ) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • A.indicator f t) =
      A.indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) := by
  classical
  funext t
  by_cases ht : t ∈ A <;> simp [ht, smul_eq_mul]

theorem mellin_indicator_Ioc (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (f : ℝ → ℂ) (s : ℂ) :
    mellin ((Ioc a b).indicator f) s =
      ∫ t : ℝ in a..b, (t : ℂ) ^ (s - 1) * f t := by
  have hsub : Ioc a b ⊆ Ioi (0 : ℝ) := fun _ ht => lt_of_le_of_lt ha ht.1
  unfold mellin
  rw [weighted_indicator, MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.Measure.restrict_restrict_of_subset hsub,
    ← intervalIntegral.integral_of_le hab]

lemma convergent_indicator_Ioc (a b : ℝ) (f : ℝ → ℂ) (s : ℂ)
    (h : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) volume a b) :
    MellinConvergent ((Ioc a b).indicator f) s := by
  unfold MellinConvergent
  rw [weighted_indicator]
  exact (h.1.integrable_indicator measurableSet_Ioc).integrableOn

lemma power_integrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (r : ℂ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ r) volume a b :=
  intervalIntegral.intervalIntegrable_cpow (Or.inr (zero_not_uIcc ha hab))

lemma left_weight (s : ℂ) (t : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) * (4 * (1 - (t : ℂ)⁻¹)) =
      4 * (t : ℂ) ^ (s - 1) - 4 * (t : ℂ) ^ (s - 2) := by
  calc
    _ = 4 * (t : ℂ) ^ (s - 1) - 4 * ((t : ℂ) ^ (s - 1) / (t : ℂ)) := by ring
    _ = _ := by rw [cpow_div_base t ht s]

lemma right_weight (s : ℂ) (t : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) * (4 / (t : ℂ) - 2) =
      4 * (t : ℂ) ^ (s - 2) - 2 * (t : ℂ) ^ (s - 1) := by
  calc
    _ = 4 * ((t : ℂ) ^ (s - 1) / (t : ℂ)) - 2 * (t : ℂ) ^ (s - 1) := by ring
    _ = _ := by rw [cpow_div_base t ht s]

lemma left_integrable (s : ℂ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      (4 * (1 - (t : ℂ)⁻¹))) volume 1 (4 / 3 : ℝ) := by
  have h1 := power_integrable 1 (4 / 3) (by norm_num) (by norm_num) (s - 1)
  have h2 := power_integrable 1 (4 / 3) (by norm_num) (by norm_num) (s - 2)
  apply ((h1.const_mul 4).sub (h2.const_mul 4)).congr
  intro t ht
  rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 4 / 3)] at ht
  exact (left_weight s t (by linarith [ht.1])).symm

lemma right_integrable (s : ℂ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      (4 / (t : ℂ) - 2)) volume (4 / 3 : ℝ) 2 := by
  have h1 := power_integrable (4 / 3) 2 (by norm_num) (by norm_num) (s - 1)
  have h2 := power_integrable (4 / 3) 2 (by norm_num) (by norm_num) (s - 2)
  apply ((h2.const_mul 4).sub (h1.const_mul 2)).congr
  intro t ht
  rw [uIoc_of_le (by norm_num : (4 / 3 : ℝ) ≤ 2)] at ht
  exact (right_weight s t (by linarith [ht.1])).symm

theorem tent_mellin_convergent (s : ℂ) : MellinConvergent tent s := by
  have h1 := convergent_indicator_Ioc 1 (4 / 3)
    (fun t : ℝ => 4 * (1 - (t : ℂ)⁻¹)) s (left_integrable s)
  have h2 := convergent_indicator_Ioc (4 / 3) 2
    (fun t : ℝ => 4 / (t : ℂ) - 2) s (right_integrable s)
  have he : tent = pieces := funext tent_eq_pieces
  rw [he]
  exact (hasMellin_add h1 h2).1

theorem mellin_intervals (s : ℂ) : mellin tent s =
    (∫ t : ℝ in 1..(4 / 3 : ℝ),
      (4 * (t : ℂ) ^ (s - 1) - 4 * (t : ℂ) ^ (s - 2))) +
    (∫ t : ℝ in (4 / 3 : ℝ)..2,
      (4 * (t : ℂ) ^ (s - 2) - 2 * (t : ℂ) ^ (s - 1))) := by
  have h1 := convergent_indicator_Ioc 1 (4 / 3)
    (fun t : ℝ => 4 * (1 - (t : ℂ)⁻¹)) s (left_integrable s)
  have h2 := convergent_indicator_Ioc (4 / 3) 2
    (fun t : ℝ => 4 / (t : ℂ) - 2) s (right_integrable s)
  have he : tent = pieces := funext tent_eq_pieces
  rw [he]
  change mellin (fun t => _ + _) s = _
  rw [(hasMellin_add h1 h2).2,
    mellin_indicator_Ioc 1 (4 / 3) (by norm_num) (by norm_num),
    mellin_indicator_Ioc (4 / 3) 2 (by norm_num) (by norm_num)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4 / 3)] at ht
    exact left_weight s t (by linarith [ht.1])
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (4 / 3 : ℝ) ≤ 2)] at ht
    exact right_weight s t (by linarith [ht.1])

lemma integral_shift_one (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (s : ℂ) (hs0 : s ≠ 0) :
    (∫ t : ℝ in a..b, (t : ℂ) ^ (s - 1)) =
      ((b : ℂ) ^ s - (a : ℂ) ^ s) / s := by
  have hr : s - 1 ≠ -1 := by
    intro h
    apply hs0
    calc
      s = (s - 1) + 1 := by ring
      _ = 0 := by rw [h]; ring
  simpa only [sub_add_cancel] using
    (integral_cpow (a := a) (b := b) (r := s - 1)
      (Or.inr ⟨hr, zero_not_uIcc ha hab⟩))

lemma integral_shift_two (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (s : ℂ) (hs1 : s ≠ 1) :
    (∫ t : ℝ in a..b, (t : ℂ) ^ (s - 2)) =
      ((b : ℂ) ^ (s - 1) - (a : ℂ) ^ (s - 1)) / (s - 1) := by
  have hr : s - 2 ≠ -1 := by
    intro h
    apply hs1
    calc
      s = (s - 2) + 2 := by ring
      _ = 1 := by rw [h]; ring
  have he : s - 2 + 1 = s - 1 := by ring
  simpa only [he] using
    (integral_cpow (a := a) (b := b) (r := s - 2)
      (Or.inr ⟨hr, zero_not_uIcc ha hab⟩))

theorem mellin_eq_multiplier (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    mellin tent s = TentMultiplier.multiplier s := by
  have h11 := power_integrable 1 (4 / 3) (by norm_num) (by norm_num) (s - 1)
  have h12 := power_integrable 1 (4 / 3) (by norm_num) (by norm_num) (s - 2)
  have h21 := power_integrable (4 / 3) 2 (by norm_num) (by norm_num) (s - 1)
  have h22 := power_integrable (4 / 3) 2 (by norm_num) (by norm_num) (s - 2)
  rw [mellin_intervals,
    intervalIntegral.integral_sub (h11.const_mul 4) (h12.const_mul 4),
    intervalIntegral.integral_sub (h22.const_mul 4) (h21.const_mul 2)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [integral_shift_one 1 (4 / 3) (by norm_num) (by norm_num) s hs0,
    integral_shift_two 1 (4 / 3) (by norm_num) (by norm_num) s hs1,
    integral_shift_two (4 / 3) 2 (by norm_num) (by norm_num) s hs1,
    integral_shift_one (4 / 3) 2 (by norm_num) (by norm_num) s hs0]
  have hb : ((4 / 3 : ℝ) : ℂ) ^ s =
      ((4 / 3 : ℝ) : ℂ) ^ (s - 1) * ((4 / 3 : ℝ) : ℂ) := by
    simpa only [sub_add_cancel, Complex.cpow_one] using
      (Complex.cpow_add (s - 1) (1 : ℂ)
        (by norm_num : ((4 / 3 : ℝ) : ℂ) ≠ 0))
  have h2 : (2 : ℂ) ^ s = (2 : ℂ) ^ (s - 1) * (2 : ℂ) := by
    simpa only [sub_add_cancel, Complex.cpow_one] using
      (Complex.cpow_add (s - 1) (1 : ℂ) (by norm_num : (2 : ℂ) ≠ 0))
  simp only [Complex.ofReal_one, Complex.ofReal_ofNat, Complex.one_cpow]
  rw [hb, h2]
  unfold TentMultiplier.multiplier TentMultiplier.numerator
  norm_num
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

theorem tent_mellin_ne_zero (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin tent s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at h0
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at h1
  rw [mellin_eq_multiplier s hs0 hs1]
  exact TentMultiplier.multiplier_ne_zero s h0 h1

end TentMellin

