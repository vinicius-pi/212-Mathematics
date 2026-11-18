import Mathematics212.PowerKernelTransfer
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Stieltjes Partial Summation and Polylogarithmic `L¹(dx / x)` Tail Bridge

Extends the power-decay tail bounds of `PowerKernelTransfer` to polylogarithmic decay:
1. Finite Abel / Stieltjes summation by parts for Dirichlet sums `∑_{u < n ≤ N} a(n) / n`;
2. Unconditional `IntegrableOn (fun t => G t / t) (Ici 2)` and quantitative tail bound
   `|∫ t in Ioi K, G t / t| ≤ C / (δ * (Real.log K) ^ δ)` (`K ≥ 2`, `δ > 0`) under
   `∀ t ≥ 2, |G t| ≤ C / (Real.log t) ^ (1 + δ)` (e.g. Vinogradov–Korobov decay).
-/

open MeasureTheory Set Filter

namespace Mathematics212

/-- Exact finite Abel / Stieltjes summation by parts for `∑_{u < n ≤ N} a(n) / n`,
expressed in terms of partial sums `S k = ∑_{j ∈ [1, k]} a j` (`1 ≤ u ≤ N`). -/
theorem abel_summation_inv (a : ℕ → ℝ) (u N : ℕ) (hu : 1 ≤ u) (hNu : u ≤ N) :
    let S : ℕ → ℝ := fun k => ∑ j ∈ Finset.Icc 1 k, a j
    ∑ n ∈ Finset.Ioc u N, a n / (n : ℝ) =
      S N / (N : ℝ) - S u / (u : ℝ) +
        ∑ n ∈ Finset.Ico u N, S n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro S
  induction N, hNu using Nat.le_induction with
  | base =>
      simp
  | succ N hNu ih =>
      have hN1 : 1 ≤ N := le_trans hu hNu
      have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hN1pos : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hIoc : Finset.Ioc u (N + 1) = insert (N + 1) (Finset.Ioc u N) := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnot_Ioc : (N + 1) ∉ Finset.Ioc u N := by
        simp only [Finset.mem_Ioc]
        omega
      have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot_Icc : (N + 1) ∉ Finset.Icc 1 N := by
        simp only [Finset.mem_Icc]
        omega
      have ha_diff : S (N + 1) - S N = a (N + 1) := by
        dsimp [S]
        rw [hIcc, Finset.sum_insert hnot_Icc]
        ring
      rw [hIoc, Finset.sum_insert hnot_Ioc, ih, Finset.sum_Ico_succ_top hNu]
      have hstep :
          a (N + 1) / ((N + 1 : ℕ) : ℝ) =
            (S (N + 1) / ((N + 1 : ℕ) : ℝ) - S N / (N : ℝ)) +
              S N * (1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) := by
        rw [← ha_diff]
        field_simp [hNpos, hN1pos]
        ring
      linarith

/-- Explicit antiderivative on `x ≥ 2`: `F(x) = -(δ⁻¹) * (Real.log x)^(-δ)` has derivative
`1 / (x * (Real.log x)^(1 + δ))` for `δ > 0`. -/
private lemma hasDerivAt_neg_inv_log_rpow {x δ : ℝ} (hx : 2 ≤ x) (hδ : 0 < δ) :
    HasDerivAt (fun t : ℝ => -(δ⁻¹) * (Real.log t) ^ (-δ))
      (1 / (x * (Real.log x) ^ (1 + δ))) x := by
  have hx0 : 0 < x := by linarith
  have hlog_gt1 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_deriv : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have hrpow : HasDerivAt (fun t : ℝ => (Real.log t) ^ (-δ))
      (x⁻¹ * (-δ * (Real.log x) ^ (-δ - 1))) x := by
    simpa [mul_assoc] using (hlog_deriv.rpow_const (p := -δ) (Or.inl hlog_gt1.ne'))
  have hconst := hrpow.const_mul (-(δ⁻¹))
  convert hconst using 1
  have hpow_eq : (Real.log x) ^ (-δ - 1) = ((Real.log x) ^ (1 + δ))⁻¹ := by
    rw [show (-δ - 1 : ℝ) = -(1 + δ) by ring, Real.rpow_neg hlog_gt1.le]
  rw [hpow_eq]
  field_simp [hδ.ne', hx0.ne']

/-- Under polylogarithmic decay `|G(t)| ≤ C / (log t)^(1 + δ)` for `t ≥ 2` (`δ > 0`),
`G(t) / t` is Lebesgue integrable on `[K, ∞)` for every `K ≥ 2` and satisfies the explicit
tail estimate `|∫ t in Ioi K, G t / t| ≤ C / (δ * (log K)^δ)`. -/
theorem log_decay_integrable_and_tail_bound
    {G : ℝ → ℝ} {C δ K : ℝ} (hGm : Measurable G)
    (_hC : 0 ≤ C) (hδ : 0 < δ) (hK : 2 ≤ K)
    (hG : ∀ t, 2 ≤ t → |G t| ≤ C / (Real.log t) ^ (1 + δ)) :
    IntegrableOn (fun t => G t / t) (Ioi K) ∧
      |∫ t in Ioi K, G t / t| ≤ C / (δ * (Real.log K) ^ δ) := by
  let maj : ℝ → ℝ := fun t => 1 / (t * (Real.log t) ^ (1 + δ))
  let anti : ℝ → ℝ := fun t => -(δ⁻¹) * (Real.log t) ^ (-δ)
  have hderiv : ∀ x ∈ Ici K, HasDerivAt anti (maj x) x := by
    intro x hx
    exact hasDerivAt_neg_inv_log_rpow (le_trans hK hx) hδ
  have hnonneg : ∀ x ∈ Ici K, 0 ≤ maj x := by
    intro x hx
    have hx2 : 2 ≤ x := le_trans hK hx
    have hxpos : 0 < x := by linarith
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    dsimp [maj]
    positivity
  have htend : Tendsto anti atTop (nhds 0) := by
    have hlog_top : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    have hrpow_zero : Tendsto (fun u : ℝ => u ^ (-δ)) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hδ
    have hcomp := hrpow_zero.comp hlog_top
    simpa [anti] using hcomp.const_mul (-(δ⁻¹))
  have hmaj_int : IntegrableOn maj (Ioi K) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => hnonneg x hx.out.le) htend
  have hmaj_val : ∫ t in Ioi K, maj t = (0 : ℝ) - anti K :=
    integral_Ioi_of_hasDerivAt_of_nonneg' hderiv (fun x hx => hnonneg x hx.out.le) htend
  have hlogK_pos : 0 < Real.log K := Real.log_pos (by linarith)
  have hmaj_eval : ∫ t in Ioi K, maj t = 1 / (δ * (Real.log K) ^ δ) := by
    rw [hmaj_val]
    dsimp [anti]
    rw [Real.rpow_neg hlogK_pos.le]
    field_simp [hδ.ne']
    ring
  have hC_maj : IntegrableOn (fun t => C * maj t) (Ioi K) := hmaj_int.const_mul C
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioi K), ‖G t / t‖ ≤ C * maj t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht2 : 2 ≤ t := le_trans hK ht.le
    have htpos : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
    calc
      |G t| / t ≤ (C / (Real.log t) ^ (1 + δ)) / t :=
        div_le_div_of_nonneg_right (hG t ht2) htpos.le
      _ = C * maj t := by
        dsimp [maj]
        ring
  have hG_int : IntegrableOn (fun t => G t / t) (Ioi K) :=
    hC_maj.mono' (hGm.div measurable_id).aestronglyMeasurable hnorm
  have hint_le : |∫ t in Ioi K, G t / t| ≤ ∫ t in Ioi K, C * maj t := by
    simpa [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_of_norm_le hC_maj hnorm
  have hC_eval : ∫ t in Ioi K, C * maj t = C / (δ * (Real.log K) ^ δ) := by
    rw [integral_const_mul, hmaj_eval]
    ring
  exact ⟨hG_int, hC_eval ▸ hint_le⟩

end Mathematics212
