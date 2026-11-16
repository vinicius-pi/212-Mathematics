import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Ring

/-!
# Vaughan Decomposition Identity for the Von Mangoldt Function

Formalizes Vaughan's exact Dirichlet-convolution algebraic identity on `ArithmeticFunction ℝ`
with truncation parameter `h : ℕ`.
-/

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RhAstraSynthesis

noncomputable def truncate (f : ArithmeticFunction ℝ) (h : ℕ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ h then f n else 0, by simp⟩

theorem actual_vaughan (h : ℕ) :
    ArithmeticFunction.vonMangoldt =
      truncate (μ : ArithmeticFunction ℝ) h * ArithmeticFunction.log -
      truncate (μ : ArithmeticFunction ℝ) h * ζ *
        truncate ArithmeticFunction.vonMangoldt h +
      truncate ArithmeticFunction.vonMangoldt h +
      ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) h) * ζ *
        (ArithmeticFunction.vonMangoldt - truncate ArithmeticFunction.vonMangoldt h) := by
  symm
  calc
    _ = (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log +
        truncate ArithmeticFunction.vonMangoldt h -
        ((μ : ArithmeticFunction ℝ) * ζ) * truncate ArithmeticFunction.vonMangoldt h := by
      simp only [← ArithmeticFunction.zeta_mul_vonMangoldt]
      ring
    _ = ArithmeticFunction.vonMangoldt := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta,
        ArithmeticFunction.moebius_mul_log_eq_vonMangoldt, one_mul]
      ring

end RhAstraSynthesis

#print axioms RhAstraSynthesis.actual_vaughan
