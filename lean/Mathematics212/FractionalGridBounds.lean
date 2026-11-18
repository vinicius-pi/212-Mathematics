import Mathematics212.ChebyshevExponentialEnvelope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Fractional-Power Grid Sampling, Chebyshev Envelope, and √n Sharpness Witness

Formalizes the fractional-grid `{n^(-α)}` (`0 < α ≤ 1`) polynomial bounds:
1. Monotonicity and strict positivity of fractional gaps `n^(-α) - (n + 1)^(-α)`;
2. Bernoulli/concavity inequality `(1 + x)^α ≤ 1 + α x` (`x ≥ 0`, `0 < α ≤ 1`) and
   fractional Remez–Chebyshev exponential envelope `T_m(2 (L m)^(-α) / e - 1) ≤ exp(2 m √(α / L))`;
3. Explicit degree-`≤ 2m` extremal polynomial `P_{m,m}^{(1/2)}` on the `1/√n` grid
   satisfying `|P_{m,m}^{(1/2)}(1/√n)| ≤ 1` for all `n ≥ 1` and
   `|(P_{m,m}^{(1/2)})'(0)| = 2 m^(5/2) + ∑_{j=1}^m √j ≥ 2 m^(5/2) > m^2`.
-/

namespace Mathematics212

open Polynomial

/-- Positive fractional gap `(n : ℝ)^(-α) - ((n + 1 : ℕ) : ℝ)^(-α)`. -/
noncomputable def fractionalGap (α : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-α) - ((n + 1 : ℕ) : ℝ) ^ (-α)

/-- Real fractional-power Bernoulli upper bound: `(1 + x)^α ≤ 1 + α * x`
for `x ≥ 0` and `0 < α ≤ 1`. -/
theorem one_add_rpow_le_one_add_mul
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hx : 0 ≤ x) :
    (1 + x) ^ α ≤ 1 + α * x := by
  let f : ℝ → ℝ := fun t => 1 + α * t - (1 + t) ^ α
  have hdiff : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt f (α - α * (1 + t) ^ (α - 1)) t := by
    intro t ht
    have htpos : 0 < 1 + t := by
      have : 0 ≤ t := ht
      linarith
    have h1 : HasDerivAt (fun u : ℝ => 1 + α * u) α t := by
      simpa using ((hasDerivAt_id t).const_mul α).const_add 1
    have h2 : HasDerivAt (fun u : ℝ => (1 + u) ^ α) (α * (1 + t) ^ (α - 1)) t := by
      have hid : HasDerivAt (fun u : ℝ => 1 + u) 1 t := (hasDerivAt_id t).const_add 1
      simpa [mul_comm, mul_left_comm, mul_assoc] using (hid.rpow_const (p := α) (Or.inl htpos.ne'))
    exact h1.sub h2
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hdiff t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht_mem : t ∈ Set.Ici (0 : ℝ) := interior_subset ht
      have hderiv : deriv f t = α - α * (1 + t) ^ (α - 1) := (hdiff t ht_mem).deriv
      rw [hderiv]
      have hbase : (1 : ℝ) ≤ 1 + t := by linarith [Set.mem_Ici.mp ht_mem]
      have hpow : (1 + t) ^ (α - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
      nlinarith [hα0]
  have hf := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hf
  dsimp [f] at hf
  linarith

/-- For `0 < α` and `n ≥ 1`, `fractionalGap α n > 0`. -/
theorem fractional_gap_pos {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    0 < fractionalGap α n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
  have hpow : ((n + 1 : ℕ) : ℝ) ^ (-α) < (n : ℝ) ^ (-α) :=
    Real.rpow_lt_rpow_of_neg hnpos hlt (by linarith)
  unfold fractionalGap
  linarith

/-- For `0 < α`, the fractional gap sequence `n ↦ n^(-α) - (n + 1)^(-α)` is
antitone on `[1, ∞)`. -/
theorem fractional_gap_antitone {α : ℝ} (hα : 0 < α) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    fractionalGap α n ≤ fractionalGap α m := by
  let g : ℝ → ℝ := fun t => t ^ (-α) - (t + 1) ^ (-α)
  have hdiff : ∀ t ∈ Set.Ici (1 : ℝ),
      HasDerivAt g ((-α) * t ^ (-α - 1) - (-α) * (t + 1) ^ (-α - 1)) t := by
    intro t ht
    have ht1 : 1 ≤ t := ht
    have htpos : 0 < t := by linarith
    have ht1pos : 0 < t + 1 := by linarith
    have hd1 : HasDerivAt (fun u : ℝ => u ^ (-α)) ((-α) * t ^ (-α - 1)) t := by
      simpa using (hasDerivAt_id t).rpow_const (p := -α) (Or.inl htpos.ne')
    have hd2 : HasDerivAt (fun u : ℝ => (u + 1) ^ (-α)) ((-α) * (t + 1) ^ (-α - 1)) t := by
      have hid : HasDerivAt (fun u : ℝ => u + 1) 1 t := (hasDerivAt_id t).add_const 1
      simpa using hid.rpow_const (p := -α) (Or.inl ht1pos.ne')
    exact hd1.sub hd2
  have hanti : AntitoneOn g (Set.Ici (1 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · exact fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hdiff t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht_mem : t ∈ Set.Ici (1 : ℝ) := interior_subset ht
      have hderiv : deriv g t = (-α) * t ^ (-α - 1) - (-α) * (t + 1) ^ (-α - 1) :=
        (hdiff t ht_mem).deriv
      rw [hderiv]
      have htpos : (0 : ℝ) < t := by linarith [Set.mem_Ici.mp ht_mem]
      have hpow : (t + 1) ^ (-α - 1) ≤ t ^ (-α - 1) :=
        Real.rpow_le_rpow_of_nonpos htpos (by linarith) (by linarith)
      nlinarith [hα]
  have hm1 : (m : ℝ) ∈ Set.Ici (1 : ℝ) := Set.mem_Ici.mpr (by exact_mod_cast hm)
  have hn1 : (n : ℝ) ∈ Set.Ici (1 : ℝ) := Set.mem_Ici.mpr (by exact_mod_cast (le_trans hm hmn))
  have hle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  simpa [g, fractionalGap, Nat.cast_add, Nat.cast_one] using hanti hm1 hn1 hle

/-- Telescoping identity for fractional bad-gap sums:
`∑_{j ∈ [k, k+m)} (j^(-α) - (j+1)^(-α)) = k^(-α) - (k+m)^(-α)`. -/
theorem fractional_gap_sum_telescope (α : ℝ) (k m : ℕ) :
    ∑ j ∈ Finset.Ico k (k + m), fractionalGap α j =
      (k : ℝ) ^ (-α) - ((k + m : ℕ) : ℝ) ^ (-α) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show k + (m + 1) = k + m + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
      simp [fractionalGap, add_assoc]

/-- Fractional Remez–Chebyshev exponential envelope for `0 < α ≤ 1`:
for `((L*m + m)^(-α)) ≤ e ≤ ((L*m)^(-α))` (`L > 0`, `m > 0`),
`T_m(2 (L*m)^(-α) / e - 1) ≤ exp(2 m √(α / L))`. -/
theorem fractional_remez_chebyshev_envelope
    (m : ℕ) {α L e : ℝ}
    (hm : 0 < (m : ℝ)) (hα0 : 0 < α) (hα1 : α ≤ 1) (hL : 0 < L)
    (he_low : ((L * (m : ℝ) + (m : ℝ)) ^ (-α)) ≤ e)
    (he_high : e ≤ ((L * (m : ℝ)) ^ (-α))) :
    (Chebyshev.T ℝ m).eval (2 * ((L * (m : ℝ)) ^ (-α)) / e - 1) ≤
      Real.exp (2 * (m : ℝ) * Real.sqrt (α / L)) := by
  have hLm_pos : 0 < L * (m : ℝ) := mul_pos hL hm
  have hLmm_pos : 0 < L * (m : ℝ) + (m : ℝ) := add_pos hLm_pos hm
  have he_low_pos : 0 < (L * (m : ℝ) + (m : ℝ)) ^ (-α) := Real.rpow_pos_of_pos hLmm_pos _
  have he_pos : 0 < e := lt_of_lt_of_le he_low_pos he_low
  have hratio_ge : 1 ≤ ((L * (m : ℝ)) ^ (-α)) / e :=
    (one_le_div he_pos).mpr he_high
  have hdiv_le :
      ((L * (m : ℝ)) ^ (-α)) / e ≤ ((L * (m : ℝ) + (m : ℝ)) / (L * (m : ℝ))) ^ α := by
    calc
      ((L * (m : ℝ)) ^ (-α)) / e
          ≤ ((L * (m : ℝ)) ^ (-α)) / ((L * (m : ℝ) + (m : ℝ)) ^ (-α)) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hLm_pos.le _) he_low_pos he_low
      _ = ((L * (m : ℝ) + (m : ℝ)) ^ α) / ((L * (m : ℝ)) ^ α) := by
        rw [Real.rpow_neg hLm_pos.le, Real.rpow_neg hLmm_pos.le]
        field_simp
      _ = ((L * (m : ℝ) + (m : ℝ)) / (L * (m : ℝ))) ^ α := by
        rw [← Real.div_rpow hLmm_pos.le hLm_pos.le]
  have hfrac : (L * (m : ℝ) + (m : ℝ)) / (L * (m : ℝ)) = 1 + 1 / L := by
    field_simp [hL.ne', hm.ne']
  have hbern : (1 + 1 / L) ^ α ≤ 1 + α * (1 / L) :=
    one_add_rpow_le_one_add_mul hα0 hα1 (by positivity)
  have harg_ge1 : 1 ≤ 2 * ((L * (m : ℝ)) ^ (-α)) / e - 1 := by
    have : 2 * ((L * (m : ℝ)) ^ (-α)) / e = 2 * (((L * (m : ℝ)) ^ (-α)) / e) := by ring
    linarith
  have harg_le : 2 * ((L * (m : ℝ)) ^ (-α)) / e - 1 ≤ 1 + 2 / (L / α) := by
    rw [hfrac] at hdiv_le
    have h1 : ((L * (m : ℝ)) ^ (-α)) / e ≤ 1 + α * (1 / L) := hdiv_le.trans hbern
    have h2 : 2 * (1 + α * (1 / L)) - 1 = 1 + 2 / (L / α) := by
      field_simp [hL.ne', hα0.ne']
      ring
    calc
      2 * ((L * (m : ℝ)) ^ (-α)) / e - 1
          = 2 * (((L * (m : ℝ)) ^ (-α)) / e) - 1 := by ring
      _ ≤ 2 * (1 + α * (1 / L)) - 1 := by linarith
      _ = 1 + 2 / (L / α) := h2
  have hL'_pos : 0 < L / α := div_pos hL hα0
  have hT_mono := chebyshev_T_mono_of_one_le m harg_ge1 harg_le
  have hT_exp := chebyshev_T_one_add_two_div_le_exp m hL'_pos
  have hsqrt : (1 : ℝ) / Real.sqrt (L / α) = Real.sqrt (α / L) := by
    rw [one_div, ← Real.sqrt_inv, inv_div]
  calc
    (Chebyshev.T ℝ m).eval (2 * ((L * (m : ℝ)) ^ (-α)) / e - 1)
        ≤ (Chebyshev.T ℝ m).eval (1 + 2 / (L / α)) := hT_mono
    _ ≤ Real.exp (2 * (m : ℝ) / Real.sqrt (L / α)) := hT_exp
    _ = Real.exp (2 * (m : ℝ) * Real.sqrt (α / L)) := by
      congr 1
      rw [div_eq_mul_inv, ← one_div, hsqrt]

/-- Explicit sharpness witness for the fractional `1/√n` grid:
`sqrtSharpnessWitness k ℓ (t) = (∏_{j=1}^k (1 - √j * t)) * T_ℓ(1 - 2 √k * t)`. -/
noncomputable def sqrtSharpnessWitness (k ℓ : ℕ) : Polynomial ℝ :=
  (∏ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X)) *
    (Chebyshev.T ℝ ℓ).comp (1 - C (2 * Real.sqrt k) * X)

theorem sqrtSharpnessWitness_natDegree_le (k ℓ : ℕ) :
    (sqrtSharpnessWitness k ℓ).natDegree ≤ k + ℓ := by
  unfold sqrtSharpnessWitness
  have hlin_deg : ∀ c : ℝ, (1 - C c * X).natDegree ≤ 1 := by
    intro c
    calc
      (1 - C c * X).natDegree ≤ max (1 : ℝ[X]).natDegree (C c * X).natDegree :=
        natDegree_sub_le _ _
      _ ≤ max 0 ((C c).natDegree + X.natDegree) := by
        gcongr
        · simp
        · exact natDegree_mul_le
      _ ≤ 1 := by simp
  have hprod_deg : (∏ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X)).natDegree ≤ k := by
    calc
      (∏ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X)).natDegree
          ≤ ∑ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X).natDegree :=
        natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 k, (1 : ℕ) := by
        refine Finset.sum_le_sum fun j _ => hlin_deg (Real.sqrt j)
      _ = k := by simp
  have hT_deg : (Chebyshev.T ℝ ℓ).natDegree ≤ ℓ :=
    natDegree_le_of_degree_le (by simp [Chebyshev.degree_T])
  have hcomp_deg : ((Chebyshev.T ℝ ℓ).comp (1 - C (2 * Real.sqrt k) * X)).natDegree ≤ ℓ := by
    calc
      ((Chebyshev.T ℝ ℓ).comp (1 - C (2 * Real.sqrt k) * X)).natDegree
          ≤ (Chebyshev.T ℝ ℓ).natDegree * (1 - C (2 * Real.sqrt k) * X).natDegree :=
        natDegree_comp_le
      _ ≤ ℓ * 1 := mul_le_mul hT_deg (hlin_deg _) (Nat.zero_le _) (Nat.zero_le _)
      _ = ℓ := mul_one _
  calc
    ((∏ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X)) *
        (Chebyshev.T ℝ ℓ).comp (1 - C (2 * Real.sqrt k) * X)).natDegree
        ≤ (∏ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X)).natDegree +
          ((Chebyshev.T ℝ ℓ).comp (1 - C (2 * Real.sqrt k) * X)).natDegree :=
      natDegree_mul_le
    _ ≤ k + ℓ := add_le_add hprod_deg hcomp_deg

theorem sqrtSharpnessWitness_eval_inv_sqrt_abs_le_one
    (k ℓ n : ℕ) (hn : 1 ≤ n) :
    |(sqrtSharpnessWitness k ℓ).eval (1 / Real.sqrt n)| ≤ 1 := by
  unfold sqrtSharpnessWitness
  rw [eval_mul, eval_prod, eval_comp]
  by_cases hnk : n ≤ k
  · have hmem : n ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hn, hnk⟩
    have hfactor0 : (1 - C (Real.sqrt n) * X).eval (1 / Real.sqrt n) = 0 := by
      have hsq_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, one_div]
      rw [mul_inv_cancel₀ hsq_pos.ne', sub_self]
    rw [Finset.prod_eq_zero hmem hfactor0, zero_mul, abs_zero]
    norm_num
  · have hnk_gt : k < n := lt_of_not_ge hnk
    have hsq_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hprod_le :
        |∏ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n)| ≤ 1 := by
      rw [Finset.abs_prod]
      have hfactor_bound :
          ∀ j ∈ Finset.Icc 1 k,
            |(1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n)| ≤ 1 := by
        intro j hj
        have hj_le_k : j ≤ k := (Finset.mem_Icc.mp hj).2
        have hj_lt_n : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans hj_le_k hnk_gt.le)
        have hj_le_sq : Real.sqrt j ≤ Real.sqrt n := Real.sqrt_le_sqrt hj_lt_n
        have hratio_nonneg : 0 ≤ Real.sqrt j / Real.sqrt n := by positivity
        have hratio_le1 : Real.sqrt j / Real.sqrt n ≤ 1 :=
          (div_le_one hsq_pos).mpr hj_le_sq
        have hev : (1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n) =
            1 - Real.sqrt j / Real.sqrt n := by
          simp [eval_sub, eval_one, eval_mul, eval_C, eval_X, div_eq_mul_inv]
        rw [hev, abs_of_nonneg (by linarith)]
        linarith
      have hprod_aux :
          ∀ s : Finset ℕ,
            (∀ j ∈ s, |(1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n)| ≤ 1) →
            (∏ j ∈ s, |(1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n)|) ≤ 1 := by
        intro s hs
        induction s using Finset.induction_on with
        | empty => simp
        | @insert j s hj ih =>
            rw [Finset.prod_insert hj]
            have h1 : |(1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n)| ≤ 1 :=
              hs j (Finset.mem_insert_self j s)
            have h2 : (∏ i ∈ s, |(1 - C (Real.sqrt i) * X).eval (1 / Real.sqrt n)|) ≤ 1 :=
              ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
            have h1_nonneg : 0 ≤ |(1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n)| := abs_nonneg _
            have h2_nonneg : 0 ≤ ∏ i ∈ s, |(1 - C (Real.sqrt i) * X).eval (1 / Real.sqrt n)| :=
              Finset.prod_nonneg fun _ _ => abs_nonneg _
            nlinarith
      exact hprod_aux (Finset.Icc 1 k) hfactor_bound
    have harg_le1 : |(1 - C (2 * Real.sqrt k) * X).eval (1 / Real.sqrt n)| ≤ 1 := by
      have hk_le_n : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnk_gt.le
      have hsq_le : Real.sqrt k ≤ Real.sqrt n := Real.sqrt_le_sqrt hk_le_n
      have hr_nonneg : 0 ≤ Real.sqrt k / Real.sqrt n := by positivity
      have hr_le1 : Real.sqrt k / Real.sqrt n ≤ 1 := (div_le_one hsq_pos).mpr hsq_le
      have hev : (1 - C (2 * Real.sqrt k) * X).eval (1 / Real.sqrt n) =
          1 - 2 * (Real.sqrt k / Real.sqrt n) := by
        simp [eval_sub, eval_one, eval_mul, eval_C, eval_X]
        ring
      rw [hev, abs_le]
      constructor <;> linarith
    have hT_le : |((Chebyshev.T ℝ ℓ).eval ((1 - C (2 * Real.sqrt k) * X).eval (1 / Real.sqrt n)))| ≤ 1 :=
      Chebyshev.abs_eval_T_real_le_one (ℓ : ℤ) harg_le1
    rw [abs_mul]
    calc
      |∏ j ∈ Finset.Icc 1 k, (1 - C (Real.sqrt j) * X).eval (1 / Real.sqrt n)| *
          |(Chebyshev.T ℝ ℓ).eval ((1 - C (2 * Real.sqrt k) * X).eval (1 / Real.sqrt n))|
          ≤ 1 * 1 := mul_le_mul hprod_le hT_le (abs_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

private lemma prod_one_sub_C_eval_zero (s : Finset ℕ) (f : ℕ → ℝ) :
    (∏ j ∈ s, (1 - C (f j) * X)).eval 0 = 1 := by
  simp [eval_prod]

private lemma prod_one_sub_C_derivative_eval_zero (s : Finset ℕ) (f : ℕ → ℝ) :
    (derivative (∏ j ∈ s, (1 - C (f j) * X))).eval 0 = -∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, derivative_mul, eval_add, eval_mul, eval_mul,
        prod_one_sub_C_eval_zero, ih]
      have ha_ev : (1 - C (f a) * X).eval 0 = 1 := by simp
      have ha_der : (derivative (1 - C (f a) * X)).eval 0 = -f a := by
        simp [derivative_sub]
      rw [ha_ev, ha_der, Finset.sum_insert ha]
      ring

/-- Exact derivative at `0` and `2 m^(5/2)` sharpness lower bound for the `1/√n` grid. -/
theorem sqrtSharpnessWitness_derivative_at_zero (m : ℕ) (hm : 1 ≤ m) :
    |(derivative (sqrtSharpnessWitness m m)).eval 0| =
        2 * (m : ℝ) ^ ((5 : ℝ) / 2) + ∑ j ∈ Finset.Icc 1 m, Real.sqrt j ∧
      2 * (m : ℝ) ^ ((5 : ℝ) / 2) ≤ |(derivative (sqrtSharpnessWitness m m)).eval 0| ∧
      (m : ℝ) ^ 2 < |(derivative (sqrtSharpnessWitness m m)).eval 0| := by
  unfold sqrtSharpnessWitness
  let A : Polynomial ℝ := ∏ j ∈ Finset.Icc 1 m, (1 - C (Real.sqrt j) * X)
  let L : Polynomial ℝ := 1 - C (2 * Real.sqrt m) * X
  let B : Polynomial ℝ := (Chebyshev.T ℝ m).comp L
  have hA0 : A.eval 0 = 1 := prod_one_sub_C_eval_zero _ _
  have hAd0 : (derivative A).eval 0 = -∑ j ∈ Finset.Icc 1 m, Real.sqrt j :=
    prod_one_sub_C_derivative_eval_zero _ _
  have hL0 : L.eval 0 = 1 := by simp [L]
  have hLd0 : (derivative L).eval 0 = -(2 * Real.sqrt m) := by
    simp [L, derivative_sub]
  have hB0 : B.eval 0 = 1 := by
    simp [B, hL0, Chebyshev.T_eval_one]
  have hBd0 : (derivative B).eval 0 = -(2 * ((m : ℝ) ^ 2 * Real.sqrt m)) := by
    rw [show B = (Chebyshev.T ℝ m).comp L from rfl, derivative_comp, eval_mul, eval_comp, hL0, hLd0,
      Chebyshev.derivative_T_eval_one]
    push_cast
    ring
  have hderiv :
      (derivative (A * B)).eval 0 =
        -(2 * ((m : ℝ) ^ 2 * Real.sqrt m) + ∑ j ∈ Finset.Icc 1 m, Real.sqrt j) := by
    rw [derivative_mul, eval_add, eval_mul, eval_mul, hA0, hAd0, hB0, hBd0]
    ring
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hrpow_eq : (m : ℝ) ^ ((5 : ℝ) / 2) = (m : ℝ) ^ 2 * Real.sqrt m := by
    have hsplit : ((5 : ℝ) / 2) = (2 : ℝ) + (1 / 2 : ℝ) := by norm_num
    rw [hsplit, Real.rpow_add (by linarith), Real.rpow_two, Real.sqrt_eq_rpow]
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.Icc 1 m, Real.sqrt j :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have habs :
      |(derivative (A * B)).eval 0| =
        2 * (m : ℝ) ^ ((5 : ℝ) / 2) + ∑ j ∈ Finset.Icc 1 m, Real.sqrt j := by
    rw [hderiv, abs_neg, hrpow_eq, abs_of_nonneg (by positivity)]
  have hge_witness : 2 * (m : ℝ) ^ ((5 : ℝ) / 2) ≤ |(derivative (A * B)).eval 0| := by
    rw [habs]
    linarith
  have hsqrt_ge1 : 1 ≤ Real.sqrt m := by
    simpa using Real.sqrt_le_sqrt hm_ge1
  have hgt_sq : (m : ℝ) ^ 2 < |(derivative (A * B)).eval 0| := by
    have hm2_pos : 0 < (m : ℝ) ^ 2 := by positivity
    have h1 : (m : ℝ) ^ 2 < 2 * (m : ℝ) ^ 2 := by linarith
    have h2 : 2 * (m : ℝ) ^ 2 ≤ 2 * ((m : ℝ) ^ 2 * Real.sqrt m) := by nlinarith
    linarith [hge_witness, hrpow_eq]
  exact ⟨habs, hge_witness, hgt_sq⟩

end Mathematics212
