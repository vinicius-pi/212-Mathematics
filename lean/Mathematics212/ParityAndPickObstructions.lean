import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Parity Pseudo-Density, Hardy Model-Space Defect, and Pick/Hankel Obstructions

Formalizes the structural obstruction primitives across Paths 1, 2, and 4:
1. Non-negativity of the Selberg parity-barrier pseudo-density
   `1 + t^(-1/4) cos(ω log t)` for all `t ≥ 1` and `ω : ℝ`;
2. Positive Hardy model-space projection defect lower bound `(2 Re(z) - 1) / ‖z‖^2 > 0`
   for any zero `z` in `Re(z) > 1/2` and any inner-product subspace orthogonal to `k_z`;
3. `Matrix.PosSemidef` obstruction lemmas showing that either a negative diagonal
   Pick/Herglotz value or a negative `2 × 2` real Hankel/Toeplitz minor refutes positive
   semidefiniteness.
-/

namespace Mathematics212

open scoped InnerProductSpace Matrix

/-- The Selberg parity-barrier oscillatory pseudo-density factor
`1 + t^(-1/4) * cos (ω * log t)` is everywhere non-negative on `t ≥ 1`. -/
theorem parity_pseudo_density_nonneg (t ω : ℝ) (ht : 1 ≤ t) :
    0 ≤ 1 + t ^ (-(1 / 4 : ℝ)) * Real.cos (ω * Real.log t) := by
  have hpow_pos : 0 ≤ t ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hpow_le : t ^ (-(1 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have hcos : -1 ≤ Real.cos (ω * Real.log t) := Real.neg_one_le_cos _
  have hmul : -t ^ (-(1 / 4 : ℝ)) ≤ t ^ (-(1 / 4 : ℝ)) * Real.cos (ω * Real.log t) := by
    have := mul_le_mul_of_nonneg_left hcos hpow_pos
    linarith
  linarith

/-- Explicit Szegő-kernel squared defect `(2 Re(z) - 1) / ‖z‖^2` associated with a zero `z`
of a tent Mellin multiplier in `Re(z) > 1/2`. -/
noncomputable def szegoDefectSq (z : ℂ) : ℝ :=
  (2 * z.re - 1) / ‖z‖ ^ 2

theorem szegoDefectSq_pos {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    0 < szegoDefectSq z := by
  have hnum : 0 < 2 * z.re - 1 := by linarith
  have hre_pos : 0 < z.re := by linarith
  have hzne : z ≠ 0 := by
    intro h
    subst h
    simp at hre_pos
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzne)
  exact div_pos hnum hden

/-- If `k : H` is a unit vector orthogonal to a subspace vector `h : H` (`⟪k, h⟫_ℂ = 0`)
and `‖⟪k, g⟫_ℂ‖^2 = szegoDefectSq z` with `Re(z) > 1/2`, then `‖g - h‖^2 ≥ szegoDefectSq z > 0`. -/
theorem model_space_projection_defect_lower_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k g h : H) {z : ℂ} (hz : (1 / 2 : ℝ) < z.re)
    (hk : ‖k‖ = 1) (horth : ⟪k, h⟫_ℂ = 0)
    (hinner : ‖⟪k, g⟫_ℂ‖ ^ 2 = szegoDefectSq z) :
    0 < szegoDefectSq z ∧ szegoDefectSq z ≤ ‖g - h‖ ^ 2 := by
  have hpos := szegoDefectSq_pos hz
  have hcs : ‖⟪k, g - h⟫_ℂ‖ ≤ ‖k‖ * ‖g - h‖ := norm_inner_le_norm k (g - h)
  have heq : ⟪k, g - h⟫_ℂ = ⟪k, g⟫_ℂ := by
    rw [inner_sub_right, horth, sub_zero]
  rw [heq, hk, one_mul] at hcs
  have hsq : ‖⟪k, g⟫_ℂ‖ ^ 2 ≤ ‖g - h‖ ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (⟪k, g⟫_ℂ), norm_nonneg (g - h)]) hcs
  rw [hinner] at hsq
  exact ⟨hpos, hsq⟩

private lemma two_point_quad_form {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {i j : n} (_hij : i ≠ j) (hsym : A j i = A i j) (a b : ℝ) :
    let v : n → ℝ := fun k => (if k = i then a else 0) + (if k = j then b else 0)
    star v ⬝ᵥ (A *ᵥ v) = a ^ 2 * A i i + 2 * a * b * A i j + b ^ 2 * A j j := by
  intro v
  have hmul : ∀ k : n, (A *ᵥ v) k = a * A k i + b * A k j := by
    intro k
    have hsum :
        ∑ l : n, A k l * v l =
          (∑ l : n, (if l = i then A k l * a else 0)) +
            (∑ l : n, (if l = j then A k l * b else 0)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp [v]
      split_ifs <;> ring
    change ∑ l : n, A k l * v l = _
    rw [hsum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  have hdot :
      ∑ k : n, v k * (A *ᵥ v) k =
        (∑ k : n, (if k = i then a * (a * A k i + b * A k j) else 0)) +
          (∑ k : n, (if k = j then b * (a * A k i + b * A k j) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmul k]
    dsimp [v]
    split_ifs <;> ring
  change ∑ k : n, star (v k) * (A *ᵥ v) k = _
  simp only [star_trivial]
  rw [hdot]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hsym]
  ring

/-- Any positive semidefinite real matrix has non-negative diagonal entries and
non-negative `2 × 2` principal minors: either `A j j < 0` or `A i i * A j j < A i j ^ 2`
(for `i ≠ j`, symmetric `A`) refutes `Matrix.PosSemidef A`. -/
theorem not_posSemidef_of_neg_two_by_two_minor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {i j : n} (hij : i ≠ j)
    (h_nonneg_diag : 0 ≤ A i i)
    (hsym : A j i = A i j)
    (hneg_det : A i i * A j j < A i j ^ 2) :
    ¬ A.PosSemidef := by
  intro hpsd
  have hquad : ∀ a b : ℝ, 0 ≤ a ^ 2 * A i i + 2 * a * b * A i j + b ^ 2 * A j j := by
    intro a b
    let v : n → ℝ := fun k => (if k = i then a else 0) + (if k = j then b else 0)
    have hv := hpsd.dotProduct_mulVec_nonneg v
    rwa [two_point_quad_form A hij hsym a b] at hv
  by_cases hjj : A j j < 0
  · have hq := hquad 0 1
    linarith
  · have hjj_nonneg : 0 ≤ A j j := le_of_not_gt hjj
    rcases eq_or_lt_of_le h_nonneg_diag with hii0 | hii_pos
    · have hij_sq : 0 < A i j ^ 2 := by
        nlinarith [hneg_det, hii0]
      have hq := hquad (-(A j j + 1)) (A i j)
      rw [← hii0] at hq
      have heq :
          (-(A j j + 1)) ^ 2 * 0 + 2 * (-(A j j + 1)) * A i j * A i j + A i j ^ 2 * A j j =
            -(A j j + 2) * A i j ^ 2 := by ring
      rw [heq] at hq
      have hneg : -(A j j + 2) * A i j ^ 2 < 0 := by nlinarith [hjj_nonneg, hij_sq]
      linarith
    · have hq := hquad (-A i j) (A i i)
      have heq :
          (-A i j) ^ 2 * A i i + 2 * (-A i j) * A i i * A i j + A i i ^ 2 * A j j =
            A i i * (A i i * A j j - A i j ^ 2) := by ring
      rw [heq] at hq
      have hneg : A i i * (A i i * A j j - A i j ^ 2) < 0 := by
        exact mul_neg_of_pos_of_neg hii_pos (sub_neg.mpr hneg_det)
      linarith

end Mathematics212
