import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic
import RhAstraSynthesis.CoprimeKernelBounds

/-!
# Summability of the actual coprime-kernel moments

Combines the squarefree/square decomposition from `CoprimeKernelBounds` with a
product of two convergent `p`-series to prove `coprime_kernel_base_moment_summable`
and `coprime_kernel_moment_summable` for all real `s > 1/2`, then derives the
infinite Euler product identity `coprime_kernel_moment_euler_hasProd`.
-/

namespace RhAstraSynthesis

noncomputable def coprimeKernelMomentTerm (s : ℝ) (d n : ℕ) : ℝ :=
  actualCoprimeKernel d n / (n : ℝ) ^ s

/-- Positivity of the actual moment summand, with the zero index included. -/
theorem coprime_kernel_moment_nonneg (s : ℝ) (d n : ℕ) :
    0 ≤ coprimeKernelMomentTerm s d n :=
  div_nonneg (actual_coprime_kernel_nonneg d n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

private theorem reciprocal_square_weight (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 / a) / ((b ^ 2 * a) ^ s) = a ^ (-(1 + s)) * b ^ (-(2 * s)) := by
  rw [one_div, div_eq_mul_inv, ← Real.rpow_neg (mul_nonneg (sq_nonneg b) ha.le) s,
    Real.mul_rpow (sq_nonneg b) ha.le, ← Real.rpow_natCast_mul hb.le 2 (-s),
    ← Real.rpow_neg_one a]
  calc
    _ = (a ^ (-1 : ℝ) * a ^ (-s)) * b ^ (2 * (-s)) := by ring
    _ = _ := by
      rw [← Real.rpow_add ha,
        show (-1 : ℝ) + -s = -(1 + s) by ring,
        show (2 : ℝ) * -s = -(2 * s) by ring]

private theorem paired_pseries_summable (s : ℝ) (hs : 1 / 2 < s) :
    Summable (fun ab : ℕ × ℕ ↦
      (ab.1 : ℝ) ^ (-(1 + s)) * (ab.2 : ℝ) ^ (-(2 * s))) := by
  have hA : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(1 + s))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hB : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(2 * s))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact Summable.mul_of_nonneg hA hB (fun _ ↦ by positivity) (fun _ ↦ by positivity)

set_option maxHeartbeats 800000 in
private theorem base_moment_summable_of_squarefree_parameters (s : ℝ) (hs : 1 / 2 < s)
    (a b : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (heq : ∀ n, (b n) ^ 2 * a n = n + 1)
    (hbound : ∀ n, actualCoprimeKernel 1 (n + 1) ≤ 1 / (a n : ℝ)) :
    Summable (coprimeKernelMomentTerm s 1) := by
  have hinj : Function.Injective (fun n : ℕ ↦ (a n, b n)) := by
    intro i j hij
    have hA : a i = a j := congrArg Prod.fst hij
    have hB : b i = b j := congrArg Prod.snd hij
    apply Nat.succ.inj
    calc
      i + 1 = (b i) ^ 2 * a i := (heq i).symm
      _ = (b j) ^ 2 * a j := by rw [hA, hB]
      _ = j + 1 := heq j
  have hComp := (paired_pseries_summable s hs).comp_injective hinj
  have hChosen : Summable (fun n : ℕ ↦
      (a n : ℝ) ^ (-(1 + s)) * (b n : ℝ) ^ (-(2 * s))) := by
    simpa only [Function.comp_def] using hComp
  have hShift : Summable (fun n : ℕ ↦ coprimeKernelMomentTerm s 1 (n + 1)) := by
    refine Summable.of_nonneg_of_le (fun n ↦ coprime_kernel_moment_nonneg s 1 (n + 1))
      ?_ hChosen
    intro n
    have haR : (0 : ℝ) < (a n : ℝ) := Nat.cast_pos.mpr (ha n)
    have hbR : (0 : ℝ) < (b n : ℝ) := Nat.cast_pos.mpr (hb n)
    have hrepr : ((n + 1 : ℕ) : ℝ) = (b n : ℝ) ^ 2 * (a n : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow] using
        congrArg (fun k : ℕ ↦ (k : ℝ)) (heq n).symm
    calc
      coprimeKernelMomentTerm s 1 (n + 1) ≤
          (1 / (a n : ℝ)) / (((n + 1 : ℕ) : ℝ) ^ s) :=
        div_le_div_of_nonneg_right (hbound n)
          (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) s)
      _ = (a n : ℝ) ^ (-(1 + s)) * (b n : ℝ) ^ (-(2 * s)) := by
        rw [hrepr]
        exact reciprocal_square_weight (a n : ℝ) (b n : ℝ) s haR hbR
  exact (summable_nat_add_iff (f := coprimeKernelMomentTerm s 1) 1).mp hShift

/-- Base-moment convergence is proved by an injective squarefree/square parametrization. -/
theorem coprime_kernel_base_moment_summable (s : ℝ) (hs : 1 / 2 < s) :
    Summable (coprimeKernelMomentTerm s 1) := by
  classical
  choose a b ha hb heq hsquare hbound using
    (fun n : ℕ ↦ exists_squarefree_kernel_majorant (n + 1) (Nat.succ_pos n))
  exact base_moment_summable_of_squarefree_parameters s hs a b ha hb heq hbound

/-- Every nonzero modulus has a finite actual moment above the half line. -/
theorem coprime_kernel_moment_summable (s : ℝ) (hs : 1 / 2 < s) (d : ℕ) (hd : d ≠ 0) :
    Summable (coprimeKernelMomentTerm s d) := by
  have hDom : Summable (fun n : ℕ ↦
      CoprimeMobius.psi d * coprimeKernelMomentTerm s 1 n) :=
    (coprime_kernel_base_moment_summable s hs).mul_left (CoprimeMobius.psi d)
  refine Summable.of_nonneg_of_le (fun n ↦ coprime_kernel_moment_nonneg s d n) ?_ hDom
  intro n
  have h := div_le_div_of_nonneg_right (actual_coprime_kernel_le_psi_mul_base d n hd)
    (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  simpa only [coprimeKernelMomentTerm, div_eq_mul_inv, mul_assoc] using h

/-- Euler-product factorization of the convergent coprime-kernel Dirichlet series for `s > 1/2`. -/
theorem coprime_kernel_moment_euler_hasProd (s : ℝ) (hs : 1 / 2 < s)
    (d : ℕ) (hd : d ≠ 0) :
    HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, coprimeKernelMomentTerm s d ((p : ℕ) ^ e))
      (∑' n : ℕ, coprimeKernelMomentTerm s d n) := by
  have hOne : coprimeKernelMomentTerm s d 1 = 1 := by
    have hK : actualCoprimeKernel d 1 = 1 :=
      (isMultiplicative_actualCoprimeKernelAF d).map_one
    simp [coprimeKernelMomentTerm, hK]
  have hMul : ∀ {m n : ℕ}, m.Coprime n →
      coprimeKernelMomentTerm s d (m * n) =
        coprimeKernelMomentTerm s d m * coprimeKernelMomentTerm s d n := by
    intro m n hmn
    have hK : actualCoprimeKernel d (m * n) =
        actualCoprimeKernel d m * actualCoprimeKernel d n :=
      (isMultiplicative_actualCoprimeKernelAF d).map_mul_of_coprime hmn
    simp only [coprimeKernelMomentTerm, hK, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    rw [div_mul_div_comm]
  have hNorm : Summable (fun n : ℕ ↦ ‖coprimeKernelMomentTerm s d n‖) := by
    have heq : (fun n : ℕ ↦ ‖coprimeKernelMomentTerm s d n‖) =
        coprimeKernelMomentTerm s d := by
      funext n
      rw [Real.norm_eq_abs, abs_of_nonneg (coprime_kernel_moment_nonneg s d n)]
    rw [heq]
    exact coprime_kernel_moment_summable s hs d hd
  have hZero : coprimeKernelMomentTerm s d 0 = 0 := by
    simp [coprimeKernelMomentTerm, actualCoprimeKernel]
  exact EulerProduct.eulerProduct_hasProd hOne hMul hNorm hZero

end RhAstraSynthesis
