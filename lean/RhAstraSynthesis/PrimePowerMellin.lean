import RhAstraSynthesis.TentMellin
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mellin-zeta identity for the dilated von Mangoldt tent sum

Connects the compactly supported prime-power kernel
`primePower y = ∑' n, Λ(n) * tent (n / y)`
to `mellin tent s * (-ζ'(s) / ζ(s))` for `1 < Re(s)` via dominated convergence
and L-series termwise integration.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal

namespace PrimePowerMellin

def coeff (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)

@[simp] lemma coeff_zero : coeff 0 = 0 := by simp [coeff]
@[simp] lemma coeff_one : coeff 1 = 0 := by simp [coeff]

def dilated (y : ℝ) : ℂ := ∑' n : ℕ, coeff n * TentMellin.tent (n * y)
def primePower (y : ℝ) : ℂ := ∑' n : ℕ, coeff n * TentMellin.tent (n / y)

lemma tent_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : TentMellin.tent t = 0 := by
  have h1 : t ∉ Icc 1 (4 / 3 : ℝ) := by intro h; linarith [h.1]
  have h2 : t ∉ Icc (4 / 3 : ℝ) 2 := by intro h; linarith [h.1]
  simp [TentMellin.tent, h1, h2]

lemma tent_zero_of_two_lt {t : ℝ} (ht : 2 < t) : TentMellin.tent t = 0 := by
  have h1 : t ∉ Icc 1 (4 / 3 : ℝ) := by intro h; linarith [h.2]
  have h2 : t ∉ Icc (4 / 3 : ℝ) 2 := by intro h; linarith [h.2]
  simp [TentMellin.tent, h1, h2]

theorem dilated_finite_support (y : ℝ) :
    (Function.support (fun n : ℕ => coeff n * TentMellin.tent (n * y))).Finite := by
  by_cases hy : 0 < y
  · apply (Set.finite_Iic ⌈2 / y⌉₊).subset
    intro n hn
    change coeff n * TentMellin.tent (n * y) ≠ 0 at hn
    have hny : (n : ℝ) * y ≤ 2 := by
      by_contra h
      exact hn (by rw [tent_zero_of_two_lt (lt_of_not_ge h), mul_zero])
    have hb : (n : ℝ) ≤ ⌈2 / y⌉₊ :=
      ((le_div_iff₀ hy).2 hny).trans (Nat.le_ceil _)
    exact_mod_cast hb
  · have he : (fun n : ℕ => coeff n * TentMellin.tent (n * y)) = 0 := by
      funext n
      simp [tent_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
        (Nat.cast_nonneg n) (le_of_not_gt hy))]
    rw [he]
    simp

theorem primePower_eq_dilated_inv (y : ℝ) : primePower y = dilated y⁻¹ := by
  simp only [primePower, dilated, div_eq_mul_inv]

theorem primePower_finite_support (y : ℝ) :
    (Function.support (fun n : ℕ => coeff n * TentMellin.tent (n / y))).Finite := by
  simpa only [div_eq_mul_inv] using dilated_finite_support y⁻¹

lemma dilated_summable (y : ℝ) :
    Summable (fun n : ℕ => coeff n * TentMellin.tent (n * y)) :=
  summable_of_hasFiniteSupport (dilated_finite_support y)

def kernel (s : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (s - 1) * TentMellin.tent y
def weighted (s : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (s - 1) * (coeff n * TentMellin.tent (n * y))
def normIntegral (s : ℂ) : ℝ := ∫ y : ℝ in Ioi 0, ‖kernel s y‖

lemma kernel_integrable (s : ℂ) : IntegrableOn (kernel s) (Ioi 0) := by
  simpa only [MellinConvergent, kernel, smul_eq_mul] using!
    TentMellin.tent_mellin_convergent s

lemma weighted_integrable (s : ℂ) (n : ℕ) :
    IntegrableOn (weighted s n) (Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    have hz : weighted s 0 = fun _ : ℝ => (0 : ℂ) := by
      funext y
      simp [weighted]
    rw [hz]
    exact integrableOn_zero
  · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h := (MellinConvergent.comp_mul_left hnp).2
      (TentMellin.tent_mellin_convergent s)
    simpa only [MellinConvergent, weighted, smul_eq_mul] using! h.const_smul (coeff n)

lemma weighted_factor (s : ℂ) (n : ℕ) (hn : n ≠ 0) (y : ℝ) (hy : 0 < y) :
    weighted s n y = LSeries.term coeff s n * (n : ℂ) * kernel s (n * y) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : (n : ℂ) ^ (s - 1) * (n : ℂ) = (n : ℂ) ^ s := by
    simpa only [sub_add_cancel, Complex.cpow_one] using
      (Complex.cpow_add (s - 1) (1 : ℂ) hnC).symm
  have hp : (n : ℂ) ^ s ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hnC]
  dsimp only [weighted, kernel]
  rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hnR hy.le, Complex.ofReal_natCast]
  field_simp
  rw [← hpow]
  ring

lemma weighted_norm_integral (s : ℂ) (n : ℕ) :
    (∫ y : ℝ in Ioi 0, ‖weighted s n y‖) =
      ‖LSeries.term coeff s n‖ * normIntegral s := by
  by_cases hn : n = 0
  · subst n
    simp [weighted]
  · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    calc
      _ = ∫ y : ℝ in Ioi 0,
          ‖LSeries.term coeff s n * (n : ℂ) * kernel s (n * y)‖ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        dsimp only
        rw [weighted_factor s n hn y hy]
      _ = _ := by
        simp_rw [norm_mul, Complex.norm_natCast]
        rw [integral_const_mul,
          integral_comp_mul_left_Ioi (fun y : ℝ => ‖kernel s y‖) 0 hnp]
        simp only [mul_zero, smul_eq_mul, normIntegral]
        field_simp

lemma coefficients_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (LSeries.term coeff s) := by
  simpa only [coeff, LSeriesSummable] using!
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs

lemma weighted_norm_integrals_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ y : ℝ in Ioi 0, ‖weighted s n y‖) := by
  simp_rw [weighted_norm_integral]
  exact ((summable_norm_iff).2 (coefficients_summable s hs)).mul_right _

lemma weighted_integral (s : ℂ) (n : ℕ) :
    (∫ y : ℝ in Ioi 0, weighted s n y) =
      LSeries.term coeff s n * mellin TentMellin.tent s := by
  by_cases hn : n = 0
  · subst n
    simp [weighted]
  · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    change mellin (fun y : ℝ => coeff n * TentMellin.tent (n * y)) s = _
    rw [show (fun y : ℝ => coeff n * TentMellin.tent (n * y)) =
        (fun y : ℝ => coeff n • TentMellin.tent (n * y)) from rfl,
      mellin_const_smul, mellin_comp_mul_left _ _ hnp, LSeries.term_def₀ coeff_zero]
    simp only [smul_eq_mul, Complex.ofReal_natCast]
    ring

lemma weighted_tsum (s : ℂ) (y : ℝ) :
    (∑' n : ℕ, weighted s n y) = (y : ℂ) ^ (s - 1) * dilated y := by
  simp only [weighted, dilated, tsum_mul_left]

lemma integrable_tsum_complex
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℂ}
    (hI : ∀ n, Integrable (F n) μ)
    (hS : Summable (fun n => ∫ x, ‖F n x‖ ∂μ)) :
    Integrable (fun x => ∑' n, F n x) μ := by
  refine ⟨AEStronglyMeasurable.tsum (fun n => (hI n).1), ?_⟩
  change (∫⁻ x, ‖∑' n, F n x‖ₑ ∂μ) < ∞
  calc
    (∫⁻ x, ‖∑' n, F n x‖ₑ ∂μ)
        ≤ ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ :=
      lintegral_tsum (fun n => (hI n).aestronglyMeasurable.enorm)
    _ = ∑' n, ENNReal.ofReal (∫ x, ‖F n x‖ ∂μ) :=
      tsum_congr (fun n =>
        (ofReal_integral_norm_eq_lintegral_enorm (hI n)).symm)
    _ < ∞ := hS.tsum_ofReal_lt_top

theorem dilated_mellin_convergent (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent dilated s := by
  have h := integrable_tsum_complex
    (weighted_integrable s) (weighted_norm_integrals_summable s hs)
  simpa only [weighted_tsum, MellinConvergent, IntegrableOn, smul_eq_mul] using h

theorem primePower_mellin_convergent (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent primePower (-s) := by
  have he : primePower = (fun y : ℝ => dilated y⁻¹) :=
    funext primePower_eq_dilated_inv
  rw [he]
  have h := (MellinConvergent.comp_rpow (f := dilated) (s := -s)
    (a := (-1 : ℝ)) (by norm_num)).2 (by simpa using dilated_mellin_convergent s hs)
  simpa only [Real.rpow_neg_one] using h

theorem dilated_mellin_identity (s : ℂ) (hs : 1 < s.re) :
    mellin dilated s = mellin TentMellin.tent s * LSeries coeff s := by
  have h := integral_tsum_of_summable_integral_norm
    (weighted_integrable s) (weighted_norm_integrals_summable s hs)
  simp_rw [weighted_integral, weighted_tsum] at h
  change (∑' n : ℕ, LSeries.term coeff s n * mellin TentMellin.tent s) =
    mellin dilated s at h
  rw [tsum_mul_right] at h
  simpa only [LSeries, mul_comm] using h.symm

theorem primePower_mellin_identity (s : ℂ) (hs : 1 < s.re) :
    mellin primePower (-s) = mellin TentMellin.tent s * LSeries coeff s := by
  have he : primePower = (fun y : ℝ => dilated y⁻¹) :=
    funext primePower_eq_dilated_inv
  rw [he, mellin_comp_inv, neg_neg, dilated_mellin_identity s hs]

theorem primePower_mellin_zeta (s : ℂ) (hs : 1 < s.re) :
    mellin primePower (-s) =
      mellin TentMellin.tent s * (-deriv riemannZeta s / riemannZeta s) := by
  rw [primePower_mellin_identity s hs]
  congr 1
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

theorem primePower_hasMellin (s : ℂ) (hs : 1 < s.re) :
    HasMellin primePower (-s)
      (mellin TentMellin.tent s * (-deriv riemannZeta s / riemannZeta s)) :=
  ⟨primePower_mellin_convergent s hs, primePower_mellin_zeta s hs⟩

end PrimePowerMellin

