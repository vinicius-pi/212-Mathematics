import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Tent kernel Mellin multiplier and critical-strip non-vanishing

Establishes strict concavity power gaps `1 + (1/2)^t < 2 (3/4)^t` for `0 < t < 1`
and proves that the tent Mellin multiplier `4 * numerator s / (s * (s - 1))`
is non-vanishing throughout the critical strip `0 < Re(s) < 1`.
-/

noncomputable section
namespace TentMultiplier

def numerator (s : ℂ) : ℂ :=
  1 + (2 : ℂ) ^ (s - 1) - 2 * ((4 / 3 : ℝ) : ℂ) ^ (s - 1)

def multiplier (s : ℂ) : ℂ :=
  4 * numerator s / (s * (s - 1))

theorem power_gap (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    1 + (1 / 2 : ℝ) ^ t < 2 * (3 / 4 : ℝ) ^ t := by
  have hf := (Real.strictConcaveOn_rpow ht0 ht1).2
  have h := hf
    (x := (1 / 2 : ℝ)) (by norm_num)
    (y := (1 : ℝ)) (by norm_num) (by norm_num)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [smul_eq_mul] at h
  linarith

theorem reciprocal_power_gap (sigma : ℝ) (h0 : 0 < sigma) (h1 : sigma < 1) :
    1 + (2 : ℝ) ^ (sigma - 1) <
      2 * (4 / 3 : ℝ) ^ (sigma - 1) := by
  have he : sigma - 1 = -(1 - sigma) := by ring
  calc
    1 + (2 : ℝ) ^ (sigma - 1) = 1 + (1 / 2 : ℝ) ^ (1 - sigma) := by
      rw [he, Real.rpow_neg_eq_inv_rpow]
      norm_num
    _ < 2 * (3 / 4 : ℝ) ^ (1 - sigma) := power_gap _ (by linarith) (by linarith)
    _ = 2 * (4 / 3 : ℝ) ^ (sigma - 1) := by
      rw [he, Real.rpow_neg_eq_inv_rpow]
      norm_num

theorem numerator_ne_zero (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    numerator s ≠ 0 := by
  have h2 : ‖(2 : ℂ) ^ (s - 1)‖ = (2 : ℝ) ^ (s.re - 1) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) (s - 1)
  have h43 : ‖((4 / 3 : ℝ) : ℂ) ^ (s - 1)‖ =
      (4 / 3 : ℝ) ^ (s.re - 1) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (4 / 3 : ℝ)) (by norm_num) (s - 1)
  have hr : ‖(2 : ℂ) * ((4 / 3 : ℝ) : ℂ) ^ (s - 1)‖ =
      2 * (4 / 3 : ℝ) ^ (s.re - 1) := by
    rw [norm_mul, h43]
    norm_num
  have hl : ‖1 + (2 : ℂ) ^ (s - 1)‖ ≤ 1 + (2 : ℝ) ^ (s.re - 1) := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (s - 1)‖ := norm_add_le _ _
      _ = _ := by rw [h2]; norm_num
  intro hz
  have he : 1 + (2 : ℂ) ^ (s - 1) =
      2 * ((4 / 3 : ℝ) : ℂ) ^ (s - 1) := sub_eq_zero.mp hz
  have hlt := lt_of_le_of_lt hl (reciprocal_power_gap s.re h0 h1)
  rw [he, hr] at hlt
  exact (lt_irrefl _) hlt

theorem multiplier_ne_zero (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    multiplier s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at h0
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at h1
  exact div_ne_zero (mul_ne_zero (by norm_num) (numerator_ne_zero s h0 h1))
    (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))

end TentMultiplier
