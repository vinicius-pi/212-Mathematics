import Mathematics212.MarkovChebyshevGeneral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Lagrange

/-!
# Markov's Interior Derivative Inequality on `[-1, 1]`

Formalizes A. A. Markov's 1889 interior derivative inequality and the
Bernstein / Van der Corput–Schaake inequality for real polynomials:

* `van_der_corput_schaake`: for every `θ : ℝ` and `P : ℝ[X]` with `deg P ≤ n` and
  `|P| ≤ B` on `[-1, 1]`,
  `n^2 * P(cos θ)^2 + (P'(cos θ) * sin θ)^2 ≤ n^2 * B^2`;
* `markov_interior_derivative_abs_le`: for all `x ∈ [-1, 1]`,
  `|(derivative P).eval x| ≤ (n : ℝ) ^ 2 * B`;
* `markov_iterate_derivative_interior_le`: for all `s : ℕ` and `x ∈ [-1, 1]`,
  `|(derivative^[s] P).eval x| ≤ (∏ j ∈ Finset.range s, (((n - j : ℕ) : ℝ) ^ 2)) * B`;
* `markov_interior_interval_transfer`: transport to `[0, 1 / (L * m)]`.

The interior region `|x| ≤ √(1 - 1/n^2)` follows directly from
`van_der_corput_schaake`, while the near-endpoint strips `[√(1 - 1/n^2), 1]` and
`[-1, -√(1 - 1/n^2)]` (`n ≥ 2`) use sign-definite Chebyshev–Lagrange basis
derivatives together with `Polynomial.Chebyshev.sumNodes_le_sumNodes_T`.
-/

namespace Mathematics212

open Polynomial Real

section Helpers

private lemma eq_zero_of_abs_le_zero_on_Icc {P : Polynomial ℝ} {n : ℕ}
    (hdeg : P.natDegree ≤ n) (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 0) :
    P = 0 := by
  refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.range (n + 1))
    (Chebyshev.strictAntiOn_node n).injOn ?_ ?_
  · rw [Finset.card_range]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  · intro i _
    exact abs_nonpos_iff.mp (hbounded (Chebyshev.node n i) Chebyshev.node_mem_Icc)

private lemma deriv_neg_X_comp (P : Polynomial ℝ) (x : ℝ) :
    (derivative (P.comp (-Polynomial.X))).eval x = -((derivative P).eval (-x)) := by
  have hcomp : derivative (P.comp (-Polynomial.X)) =
      (derivative P).comp (-Polynomial.X) * derivative (-Polynomial.X) := by
    simpa using (derivative_comp P (-Polynomial.X))
  rw [hcomp, eval_mul, eval_comp, derivative_neg, derivative_X, eval_neg, eval_X, eval_neg,
    eval_one]
  ring

private lemma natDegree_comp_neg_X (P : Polynomial ℝ) :
    (P.comp (-Polynomial.X)).natDegree ≤ P.natDegree := by
  calc
    (P.comp (-Polynomial.X)).natDegree
        ≤ P.natDegree * (-Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_comp_le
    _ ≤ P.natDegree * 1 := by simp
    _ = P.natDegree := mul_one _

private lemma natDegree_iterate_derivative_le (P : Polynomial ℝ) (s : ℕ) :
    (derivative^[s] P).natDegree ≤ P.natDegree - s := by
  induction s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h1 : (derivative (derivative^[k] P)).natDegree ≤ (derivative^[k] P).natDegree - 1 :=
        Polynomial.natDegree_derivative_le (derivative^[k] P)
      omega

end Helpers

section NearEndpoint

private lemma one_sub_chebyshev_node_ge (n j : ℕ) (hn : 1 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    2 * ((j : ℝ) / (n : ℝ)) ^ 2 ≤ 1 - Chebyshev.node n j := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let θ : ℝ := (j : ℝ) * Real.pi / (2 * (n : ℝ))
  have hθ_nonneg : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ_le : θ ≤ Real.pi / 2 := by
    dsimp [θ]
    have hjn' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    calc
      (j : ℝ) * Real.pi / (2 * (n : ℝ)) ≤ (n : ℝ) * Real.pi / (2 * (n : ℝ)) := by gcongr
      _ = Real.pi / 2 := by field_simp [hn_pos.ne']
  have hcos_eq : 1 - Chebyshev.node n j = 2 * (Real.sin θ) ^ 2 := by
    unfold Chebyshev.node
    have h2θ : (j : ℝ) * Real.pi / (n : ℝ) = 2 * θ := by
      dsimp [θ]
      field_simp [hn_pos.ne']
    rw [h2θ, Real.cos_two_mul]
    have hsin2 := Real.sin_sq_add_cos_sq θ
    linarith
  have hsin_low : (j : ℝ) / (n : ℝ) ≤ Real.sin θ := by
    have hmul := Real.mul_le_sin hθ_nonneg hθ_le
    have heq : 2 / Real.pi * θ = (j : ℝ) / (n : ℝ) := by
      dsimp [θ]
      field_simp [Real.pi_pos.ne', hn_pos.ne']
    linarith
  rw [hcos_eq]
  have hsq : ((j : ℝ) / (n : ℝ)) ^ 2 ≤ (Real.sin θ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin_low 2
  linarith

private lemma one_sub_x_le_near_endpoint {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx_lo : Real.sqrt (1 - 1 / (n : ℝ) ^ 2) ≤ x) (_hx_hi : x ≤ 1) :
    1 - x ≤ (5 / 9 : ℝ) / (n : ℝ) ^ 2 := by
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hrad_ge : (3 / 4 : ℝ) ≤ 1 - 1 / (n : ℝ) ^ 2 := by
    have hdiv : 1 / (n : ℝ) ^ 2 ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn2
    linarith
  have hsqrt_gt : (4 / 5 : ℝ) < Real.sqrt (1 - 1 / (n : ℝ) ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith [show ((4 / 5 : ℝ) ^ 2 : ℝ) < 3 / 4 by norm_num]
  have h1x_pos : (9 / 5 : ℝ) < 1 + x := by linarith
  have h1x_sq : 1 - x ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
    have h0 : 0 ≤ 1 - 1 / (n : ℝ) ^ 2 := by linarith
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx_lo 2
    rw [Real.sq_sqrt h0] at hsq
    linarith
  have hfac : (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
  have hdiv := div_le_div₀ (by positivity) h1x_sq (by norm_num : (0 : ℝ) < 9 / 5) h1x_pos.le
  calc
    1 - x = (1 - x ^ 2) / (1 + x) := by rw [← hfac]; field_simp [show (1 + x) ≠ 0 by linarith]
    _ ≤ (1 / (n : ℝ) ^ 2) / (9 / 5 : ℝ) := hdiv
    _ = (5 / 9 : ℝ) / (n : ℝ) ^ 2 := by ring

private lemma sum_inv_telescoping (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.Icc 2 n, ((1 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) < 1 / 2 := by
  have hterm_le : ∀ j ∈ Finset.Icc 2 n,
      ((1 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) ≤
        (1 / 2 : ℝ) * (1 / ((j : ℝ) - 1) - 1 / (j : ℝ)) := by
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjr : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
    have hden1 : 0 < 2 * (j : ℝ) ^ 2 - 5 / 9 := by nlinarith
    have hden2 : 0 < 2 * (j : ℝ) * ((j : ℝ) - 1) := by nlinarith
    have heq : (1 / 2 : ℝ) * (1 / ((j : ℝ) - 1) - 1 / (j : ℝ)) = 1 / (2 * (j : ℝ) * ((j : ℝ) - 1)) := by
      have hm1 : (j : ℝ) - 1 ≠ 0 := by linarith
      have hjne : (j : ℝ) ≠ 0 := by linarith
      field_simp [hm1, hjne]
      ring
    rw [heq]
    apply div_le_div_of_nonneg_left (by norm_num) hden2
    nlinarith
  have htele :
      ∑ j ∈ Finset.Icc 2 n, (1 / ((j : ℝ) - 1) - 1 / (j : ℝ)) = 1 - 1 / (n : ℝ) := by
    clear hterm_le
    induction n, hn using Nat.le_induction with
    | base =>
        simp only [Finset.Icc_self, Finset.sum_singleton]
        norm_num
    | succ m hm ih =>
        have hsplit : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : (m + 1) ∉ Finset.Icc 2 m := by simp [Finset.mem_Icc]
        rw [hsplit, Finset.sum_insert hnot, ih]
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
        have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
        push_cast
        field_simp [hm0, hm1]
        ring
  have hsum_le :
      ∑ j ∈ Finset.Icc 2 n, ((1 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) ≤
        (1 / 2 : ℝ) * (1 - 1 / (n : ℝ)) := by
    calc
      ∑ j ∈ Finset.Icc 2 n, ((1 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9))
          ≤ ∑ j ∈ Finset.Icc 2 n, ((1 / 2 : ℝ) * (1 / ((j : ℝ) - 1) - 1 / (j : ℝ))) :=
        Finset.sum_le_sum hterm_le
      _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 2 n, (1 / ((j : ℝ) - 1) - 1 / (j : ℝ)) := by
        rw [Finset.mul_sum]
      _ = (1 / 2 : ℝ) * (1 - 1 / (n : ℝ)) := by rw [htele]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hinv_pos : 0 < 1 / (n : ℝ) := by positivity
  linarith

private lemma prod_X_sub_C_eval_deriv {S : Finset ℕ} (v : ℕ → ℝ) (x : ℝ) :
    (derivative (∏ j ∈ S, (X - C (v j)))).eval x =
      ∑ j ∈ S, ∏ m ∈ S.erase j, (x - v m) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, derivative_mul, eval_add, eval_mul, eval_mul, ih]
      have ha_ev : (X - C (v a)).eval x = x - v a := by simp
      have ha_der : (derivative (X - C (v a))).eval x = 1 := by simp
      have hprod_ev : (∏ j ∈ s, (X - C (v j))).eval x = ∏ m ∈ s, (x - v m) := by
        rw [eval_prod]
        refine Finset.prod_congr rfl fun m _ => by simp
      rw [ha_ev, ha_der, one_mul, hprod_ev, Finset.sum_insert ha, Finset.erase_insert ha,
        add_comm]
      have hrest :
          (x - v a) * ∑ j ∈ s, ∏ m ∈ s.erase j, (x - v m) =
            ∑ j ∈ s, ∏ m ∈ (insert a s).erase j, (x - v m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : a ≠ j := fun h => ha (h ▸ hj)
        have ha_not : a ∉ s.erase j := fun h => ha (Finset.erase_subset j s h)
        rw [Finset.erase_insert_of_ne hne, Finset.prod_insert ha_not]
      rw [hrest, add_comm]

private noncomputable def chebyshevLagrangeDerivC (n : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  (derivative (Lagrange.basis (Finset.range (n + 1)) (Chebyshev.node n) i)).eval x

private lemma near_endpoint_basis_deriv_sign {n i : ℕ} (hn : 2 ≤ n) (hi : i ≤ n) {x : ℝ}
    (hx_lo : Real.sqrt (1 - 1 / (n : ℝ) ^ 2) ≤ x) (hx_hi : x ≤ 1) :
    0 ≤ (-1 : ℝ) ^ i * chebyshevLagrangeDerivC n x i := by
  classical
  unfold chebyshevLagrangeDerivC
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have h1x : 1 - x ≤ (5 / 9 : ℝ) / (n : ℝ) ^ 2 := one_sub_x_le_near_endpoint hn hx_lo hx_hi
  have hgap_pos : ∀ j ∈ Finset.Icc 1 n,
      (2 * (j : ℝ) ^ 2 - 5 / 9) / (n : ℝ) ^ 2 ≤ x - Chebyshev.node n j ∧
        0 < x - Chebyshev.node n j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hnode := one_sub_chebyshev_node_ge n j hn1 hj1 hjn
    have hsplit : (2 * (j : ℝ) ^ 2 - 5 / 9) / (n : ℝ) ^ 2 =
        2 * ((j : ℝ) / (n : ℝ)) ^ 2 - (5 / 9 : ℝ) / (n : ℝ) ^ 2 := by ring
    have hle : (2 * (j : ℝ) ^ 2 - 5 / 9) / (n : ℝ) ^ 2 ≤ x - Chebyshev.node n j := by
      linarith [hnode, h1x, hsplit]
    have hnum_pos : 0 < 2 * (j : ℝ) ^ 2 - 5 / 9 := by
      have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      nlinarith
    exact ⟨hle, lt_of_lt_of_le (div_pos hnum_pos (sq_pos_of_pos hn_pos)) hle⟩
  let S : Finset ℕ := (Finset.range (n + 1)).erase i
  have hden_pos : 0 < (-1 : ℝ) ^ i * ∏ j ∈ S, (Chebyshev.node n i - Chebyshev.node n j) :=
    Chebyshev.zero_lt_prod_node_sub_node hi
  have hinv_pos : 0 < (-1 : ℝ) ^ i * (∏ j ∈ S, (Chebyshev.node n i - Chebyshev.node n j))⁻¹ := by
    have := inv_pos_of_pos hden_pos
    rwa [mul_inv, ← inv_pow, inv_neg_one] at this
  have hbasis_eq :
      Lagrange.basis (Finset.range (n + 1)) (Chebyshev.node n) i =
        C ((∏ j ∈ S, (Chebyshev.node n i - Chebyshev.node n j))⁻¹) *
          ∏ j ∈ S, (X - C (Chebyshev.node n j)) := by
    unfold Lagrange.basis Lagrange.basisDivisor
    rw [Finset.prod_mul_distrib, ← map_prod C (fun j => (Chebyshev.node n i - Chebyshev.node n j)⁻¹) S,
      ← Finset.prod_inv_distrib]
  rw [hbasis_eq, derivative_C_mul, eval_mul, eval_C, prod_X_sub_C_eval_deriv]
  rw [← mul_assoc]
  refine mul_nonneg hinv_pos.le ?_
  by_cases hi0 : i = 0
  · refine Finset.sum_nonneg fun j _ => Finset.prod_nonneg fun m hm => ?_
    have hmS : m ∈ S := Finset.erase_subset j S hm
    have hm1 : 1 ≤ m := by
      have hne : m ≠ i := (Finset.mem_erase.mp hmS).1
      omega
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hmS).2)
    exact (hgap_pos m (Finset.mem_Icc.mpr ⟨hm1, hmn⟩)).2.le
  · have h0S : 0 ∈ S := Finset.mem_erase.mpr ⟨Ne.symm hi0, Finset.mem_range.mpr (by omega)⟩
    have hS0_sub : S.erase 0 ⊆ Finset.Icc 1 n := by
      intro m hm
      have hmS := Finset.mem_erase.mp hm
      have hmr := Finset.mem_range.mp (Finset.mem_erase.mp hmS.2).2
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hmS.1, Nat.lt_succ_iff.mp hmr⟩
    let P0 : ℝ := ∏ m ∈ S.erase 0, (x - Chebyshev.node n m)
    have hP0_pos : 0 < P0 := Finset.prod_pos fun m hm => (hgap_pos m (hS0_sub hm)).2
    have hsplit : ∑ j ∈ S, ∏ m ∈ S.erase j, (x - Chebyshev.node n m) =
        P0 * (1 - ∑ j ∈ S.erase 0, (1 - x) / (x - Chebyshev.node n j)) := by
      rw [← Finset.add_sum_erase S (fun j => ∏ m ∈ S.erase j, (x - Chebyshev.node n m)) h0S]
      have hterm : ∀ j ∈ S.erase 0,
          ∏ m ∈ S.erase j, (x - Chebyshev.node n m) =
            -((1 - x) / (x - Chebyshev.node n j)) * P0 := by
        intro j hj
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        have h0_mem : 0 ∈ S.erase j := Finset.mem_erase.mpr ⟨hj0.symm, h0S⟩
        have hgap_ne : x - Chebyshev.node n j ≠ 0 := (hgap_pos j (hS0_sub hj)).2.ne'
        have herase_comm : (S.erase j).erase 0 = (S.erase 0).erase j := by
          ext k; simp only [Finset.mem_erase]; tauto
        have hP0_fac : P0 = (x - Chebyshev.node n j) *
            ∏ m ∈ (S.erase 0).erase j, (x - Chebyshev.node n m) := by
          dsimp [P0]
          rw [← Finset.mul_prod_erase (S.erase 0) (fun m => x - Chebyshev.node n m) hj]
        rw [← Finset.mul_prod_erase (S.erase j) (fun m => x - Chebyshev.node n m) h0_mem,
          Chebyshev.node_eq_one, herase_comm, hP0_fac]
        field_simp [hgap_ne]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_neg_distrib]
      change P0 + (-(∑ j ∈ S.erase 0, (1 - x) / (x - Chebyshev.node n j)) * P0) =
        P0 * (1 - ∑ j ∈ S.erase 0, (1 - x) / (x - Chebyshev.node n j))
      ring
    rw [hsplit]
    refine mul_nonneg hP0_pos.le ?_
    have hsum_term_le : ∀ j ∈ S.erase 0,
        (1 - x) / (x - Chebyshev.node n j) ≤ (5 / 9 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9) := by
      intro j hj
      have hjIcc := hS0_sub hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjIcc).1
      have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have hnum_pos : 0 < 2 * (j : ℝ) ^ 2 - 5 / 9 := by nlinarith
      have hgap := hgap_pos j hjIcc
      have heq_rhs : (5 / 9 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9) =
          ((5 / 9 : ℝ) / (n : ℝ) ^ 2) / ((2 * (j : ℝ) ^ 2 - 5 / 9) / (n : ℝ) ^ 2) := by
        field_simp [hn_pos.ne']
      rw [heq_rhs]
      exact div_le_div₀ (by positivity) h1x (div_pos hnum_pos (sq_pos_of_pos hn_pos)) hgap.1
    have hsum_Icc1 :
        ∑ j ∈ Finset.Icc 1 n, ((5 / 9 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) ≤ 1 := by
      have h1mem : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩
      have herase1 : (Finset.Icc 1 n).erase 1 = Finset.Icc 2 n := by
        ext k; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
      rw [← Finset.add_sum_erase (Finset.Icc 1 n) _ h1mem, herase1]
      have htele := sum_inv_telescoping n hn
      have h2sum :
          ∑ j ∈ Finset.Icc 2 n, ((5 / 9 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) <
            (5 / 9 : ℝ) * (1 / 2) := by
        have hfac : ∀ j ∈ Finset.Icc 2 n,
            ((5 / 9 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) =
              (5 / 9 : ℝ) * (1 / (2 * (j : ℝ) ^ 2 - 5 / 9)) := fun j _ => by ring
        rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
        exact mul_lt_mul_of_pos_left htele (by norm_num)
      norm_num at h2sum ⊢
      linarith
    have hsum_le : ∑ j ∈ S.erase 0, (1 - x) / (x - Chebyshev.node n j) ≤ 1 := by
      calc
        ∑ j ∈ S.erase 0, (1 - x) / (x - Chebyshev.node n j)
            ≤ ∑ j ∈ S.erase 0, ((5 / 9 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) :=
          Finset.sum_le_sum hsum_term_le
        _ ≤ ∑ j ∈ Finset.Icc 1 n, ((5 / 9 : ℝ) / (2 * (j : ℝ) ^ 2 - 5 / 9)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hS0_sub fun j hj _ => ?_
          have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
          exact div_nonneg (by norm_num) (by nlinarith)
        _ ≤ 1 := hsum_Icc1
    linarith

private lemma eval_deriv_eq_sumNodes {n : ℕ} {Q : Polynomial ℝ} (hdeg : Q.natDegree ≤ n)
    (x : ℝ) :
    (derivative Q).eval x = Chebyshev.sumNodes n (chebyshevLagrangeDerivC n x) Q := by
  have hQdeg : Q.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hinterp : Q = Lagrange.interpolate (Finset.range (n + 1)) (Chebyshev.node n)
      (fun i => Q.eval (Chebyshev.node n i)) :=
    Lagrange.eq_interpolate (Chebyshev.strictAntiOn_node n).injOn hQdeg
  conv_lhs => rw [hinterp, Lagrange.interpolate_apply, derivative_sum, eval_finsetSum]
  simp_rw [derivative_C_mul, eval_mul, eval_C]
  rw [Chebyshev.sumNodes, ← Nat.range_succ_eq_Iic n]
  rfl

private lemma markov_near_endpoint_one_le {n : ℕ} (hn : 2 ≤ n) {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ n) (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1)
    {x : ℝ} (hx_lo : Real.sqrt (1 - 1 / (n : ℝ) ^ 2) ≤ x) (hx_hi : x ≤ 1) :
    |(derivative P).eval x| ≤ (n : ℝ) ^ 2 := by
  have hTdeg : (Chebyshev.T ℝ n).natDegree ≤ n := by simp
  have hx_mem : |x| ≤ 1 := by
    have h0 : 0 ≤ x := le_trans (Real.sqrt_nonneg _) hx_lo
    exact abs_le.mpr ⟨by linarith, hx_hi⟩
  have hc : ∀ i ≤ n, 0 ≤ (-1 : ℝ) ^ i * chebyshevLagrangeDerivC n x i := fun i hi =>
    near_endpoint_basis_deriv_sign hn hi hx_lo hx_hi
  have hpos : (derivative P).eval x ≤ (derivative (Chebyshev.T ℝ n)).eval x := by
    rw [eval_deriv_eq_sumNodes hdeg x, eval_deriv_eq_sumNodes hTdeg x]
    exact Chebyshev.sumNodes_le_sumNodes_T hc hbounded
  have hneg : -((derivative P).eval x) ≤ (derivative (Chebyshev.T ℝ n)).eval x := by
    have hdeg_neg : (-P).natDegree ≤ n := by simpa using hdeg
    have hb_neg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(-P).eval t| ≤ 1 := fun t ht => by
      simpa using hbounded t ht
    have h1 := Chebyshev.sumNodes_le_sumNodes_T hc hb_neg
    rw [← eval_deriv_eq_sumNodes hdeg_neg x, ← eval_deriv_eq_sumNodes hTdeg x, derivative_neg,
      eval_neg] at h1
    exact h1
  have hT1 : |(derivative (Chebyshev.T ℝ n)).eval x| ≤ (n : ℝ) ^ 2 := by
    have hT := Chebyshev.abs_iterate_derivative_T_real_le (n := (n : ℤ)) 1 hx_mem
    have hev := chebyshev_iterate_derivative_eval_one_eq n 1
    rw [Function.iterate_one] at hT hev
    simp only [Finset.range_one, Finset.prod_singleton, CharP.cast_eq_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, markovOddDenom] at hev
    norm_num at hev
    linarith
  exact le_trans (abs_le.mpr ⟨by linarith, hpos⟩) (le_trans (le_abs_self _) hT1)

private lemma markov_near_endpoint_right {n : ℕ} (hn : 2 ≤ n) (P : Polynomial ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B)
    {x : ℝ} (hx_lo : Real.sqrt (1 - 1 / (n : ℝ) ^ 2) ≤ x) (hx_hi : x ≤ 1) :
    |(derivative P).eval x| ≤ (n : ℝ) ^ 2 * B := by
  by_cases hB0 : B = 0
  · subst hB0
    rw [eq_zero_of_abs_le_zero_on_Icc hdeg hbounded]
    simp
  · have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    let Q : Polynomial ℝ := C B⁻¹ * P
    have hQdeg : Q.natDegree ≤ n := le_trans (natDegree_C_mul_le B⁻¹ P) hdeg
    have hQb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Q.eval t| ≤ 1 := by
      intro t ht
      dsimp [Q]
      rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hB_pos)]
      calc
        B⁻¹ * |P.eval t| ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hbounded t ht) (inv_nonneg.mpr hB)
        _ = 1 := inv_mul_cancel₀ hB0
    have hQ := markov_near_endpoint_one_le hn hQdeg hQb hx_lo hx_hi
    dsimp [Q] at hQ
    rw [derivative_C_mul, eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hB_pos)] at hQ
    calc
      |(derivative P).eval x| = B * (B⁻¹ * |(derivative P).eval x|) := by
        field_simp [hB0]
      _ ≤ B * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hQ hB
      _ = (n : ℝ) ^ 2 * B := mul_comm _ _

end NearEndpoint

section BernsteinVanDerCorputSchaake

private noncomputable def homogCos (β : ℝ) : Polynomial ℝ :=
  C (Real.cos β) * (1 - X ^ 2) - C (2 * Real.sin β) * X

private noncomputable def homogSin (β : ℝ) : Polynomial ℝ :=
  C (Real.sin β) * (1 - X ^ 2) + C (2 * Real.cos β) * X

private noncomputable def weierstrassHomog (β : ℝ) (m : ℕ) (R : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m + 1), C (R.coeff k) * (homogCos β) ^ k * (1 + X ^ 2) ^ (m - k)

private lemma natDegree_homogCos_le (β : ℝ) : (homogCos β).natDegree ≤ 2 := by
  unfold homogCos
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans natDegree_mul_le ?_
    simp only [natDegree_C, zero_add]
    exact le_trans (natDegree_sub_le _ _) (by simp)
  · exact le_trans (natDegree_C_mul_le (2 * Real.sin β) X) (by simp)

private lemma natDegree_homogSin_le (β : ℝ) : (homogSin β).natDegree ≤ 2 := by
  unfold homogSin
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · refine le_trans natDegree_mul_le ?_
    simp only [natDegree_C, zero_add]
    exact le_trans (natDegree_sub_le _ _) (by simp)
  · exact le_trans (natDegree_C_mul_le (2 * Real.cos β) X) (by simp)

private lemma natDegree_weierstrassHomog_le (β : ℝ) (m : ℕ) (R : Polynomial ℝ) :
    (weierstrassHomog β m R).natDegree ≤ 2 * m := by
  unfold weierstrassHomog
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine le_trans natDegree_mul_le ?_
  have h1 : (C (R.coeff k) * (homogCos β) ^ k).natDegree ≤ 2 * k := by
    refine le_trans (natDegree_C_mul_le (R.coeff k) ((homogCos β) ^ k)) ?_
    exact le_trans natDegree_pow_le (by nlinarith [natDegree_homogCos_le β])
  have h2 : ((1 + X ^ 2 : Polynomial ℝ) ^ (m - k)).natDegree ≤ 2 * (m - k) := by
    refine le_trans natDegree_pow_le ?_
    have hdeg2 : (1 + X ^ 2 : Polynomial ℝ).natDegree ≤ 2 :=
      le_trans (natDegree_add_le _ _) (by simp)
    have hmul := Nat.mul_le_mul_left (m - k) hdeg2
    linarith
  calc
    (C (R.coeff k) * (homogCos β) ^ k).natDegree +
        ((1 + X ^ 2 : Polynomial ℝ) ^ (m - k)).natDegree
        ≤ 2 * k + 2 * (m - k) := Nat.add_le_add h1 h2
    _ = 2 * m := by omega

private lemma cos_weierstrass_eq (β t : ℝ) :
    Real.cos (β + 2 * Real.arctan t) = (homogCos β).eval t / (1 + t ^ 2) := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hcos2 : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    field_simp
    ring
  have hsin2 : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hden.le
    calc
      2 * (t / Real.sqrt (1 + t ^ 2)) * (1 / Real.sqrt (1 + t ^ 2))
          = 2 * t / (Real.sqrt (1 + t ^ 2) ^ 2) := by ring
      _ = 2 * t / (1 + t ^ 2) := by rw [hsq]
  rw [Real.cos_add, hcos2, hsin2]
  unfold homogCos
  simp only [eval_sub, eval_mul, eval_C, eval_one, eval_pow, eval_X]
  ring

private lemma sin_weierstrass_eq (β t : ℝ) :
    Real.sin (β + 2 * Real.arctan t) = (homogSin β).eval t / (1 + t ^ 2) := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hcos2 : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    field_simp
    ring
  have hsin2 : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hden.le
    calc
      2 * (t / Real.sqrt (1 + t ^ 2)) * (1 / Real.sqrt (1 + t ^ 2))
          = 2 * t / (Real.sqrt (1 + t ^ 2) ^ 2) := by ring
      _ = 2 * t / (1 + t ^ 2) := by rw [hsq]
  rw [Real.sin_add, hsin2, hcos2]
  unfold homogSin
  simp only [eval_add, eval_mul, eval_C, eval_one, eval_sub, eval_pow, eval_X]
  ring

private lemma eval_weierstrassHomog (β : ℝ) (m : ℕ) (R : Polynomial ℝ) (hdeg : R.natDegree ≤ m)
    (t : ℝ) :
    (weierstrassHomog β m R).eval t =
      (1 + t ^ 2) ^ m * R.eval (Real.cos (β + 2 * Real.arctan t)) := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  rw [cos_weierstrass_eq, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum]
  unfold weierstrassHomog
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X, div_pow]
  have hpow : (1 + t ^ 2) ^ m = (1 + t ^ 2) ^ k * (1 + t ^ 2) ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkm]
  rw [hpow]
  field_simp [hden]

private lemma choose_weierstrass_shift {n : ℕ} (hn : 1 ≤ n) (α θ₀ : ℝ) :
    ∃ β : ℝ,
      (∀ (k d : ℤ), (α + (k : ℝ) * Real.pi) / (n : ℝ) ≠ β + (2 * (d : ℝ) + 1) * Real.pi) ∧
      (∀ (m d : ℤ), θ₀ + (m : ℝ) * (2 * Real.pi) ≠ β + (2 * (d : ℝ) + 1) * Real.pi) := by
  let f : ℝ → ℝ := fun u => Int.fract (u / (2 * Real.pi) - 1 / 2)
  let S₁ : Finset ℝ :=
    (Finset.range (2 * n)).image fun (j : ℕ) => f ((α + (j : ℝ) * Real.pi) / (n : ℝ))
  let S : Finset ℝ := insert (f θ₀) S₁
  have hSfin : (S : Set ℝ).Finite := S.finite_toSet
  have hdiff : (Set.Ioo (0 : ℝ) 1 \ (S : Set ℝ)).Infinite :=
    (Set.Ioo_infinite zero_lt_one).sdiff hSfin
  obtain ⟨r, hr_Ioo, hr_not⟩ := hdiff.nonempty
  have hfr : Int.fract r = r := Int.fract_eq_self.mpr ⟨hr_Ioo.1.le, hr_Ioo.2⟩
  refine ⟨2 * Real.pi * r, ?_, ?_⟩
  · intro k d hEq
    have hn_pos : (0 : ℤ) < 2 * (n : ℤ) := by omega
    have hq := (Int.mul_ediv_add_emod k (2 * (n : ℤ))).symm
    let q : ℤ := k / (2 * (n : ℤ))
    let rZ : ℤ := k % (2 * (n : ℤ))
    have hrZ0 : 0 ≤ rZ := Int.emod_nonneg k hn_pos.ne'
    have hrZ_lt : rZ < 2 * (n : ℤ) := Int.emod_lt_of_pos k hn_pos
    let j : ℕ := rZ.toNat
    have hj_lt : j < 2 * n := by omega
    have hj_cast : (j : ℤ) = rZ := Int.toNat_of_nonneg hrZ0
    have hk_eq : (k : ℝ) = 2 * (n : ℝ) * (q : ℝ) + (j : ℝ) := by
      have : k = 2 * (n : ℤ) * q + (j : ℤ) := by
        dsimp [q]
        rw [hj_cast]
        exact hq
      exact_mod_cast this
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hLHS :
        ((α + (k : ℝ) * Real.pi) / (n : ℝ)) / (2 * Real.pi) - 1 / 2 =
          ((α + (j : ℝ) * Real.pi) / (n : ℝ) / (2 * Real.pi) - 1 / 2) + (q : ℝ) := by
      rw [hk_eq]
      field_simp [hn_ne, hpi_ne]
      ring
    have hRHS :
        (2 * Real.pi * r + (2 * (d : ℝ) + 1) * Real.pi) / (2 * Real.pi) - 1 / 2 = r + (d : ℝ) := by
      field_simp [hpi_ne]
      ring
    have hdiv :
        ((α + (k : ℝ) * Real.pi) / (n : ℝ)) / (2 * Real.pi) - 1 / 2 =
          (2 * Real.pi * r + (2 * (d : ℝ) + 1) * Real.pi) / (2 * Real.pi) - 1 / 2 := by
      rw [hEq]
    rw [hLHS, hRHS] at hdiv
    have hfrac := congrArg Int.fract hdiv
    rw [Int.fract_add_intCast, Int.fract_add_intCast, hfr] at hfrac
    have hmem : r ∈ (S : Set ℝ) := by
      refine Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image.mpr ?_))
      exact ⟨j, Finset.mem_range.mpr hj_lt, by dsimp [f]; exact hfrac⟩
    exact hr_not hmem
  · intro m d hEq
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hLHS :
        (θ₀ + (m : ℝ) * (2 * Real.pi)) / (2 * Real.pi) - 1 / 2 =
          (θ₀ / (2 * Real.pi) - 1 / 2) + (m : ℝ) := by
      field_simp [hpi_ne]
      ring
    have hRHS :
        (2 * Real.pi * r + (2 * (d : ℝ) + 1) * Real.pi) / (2 * Real.pi) - 1 / 2 = r + (d : ℝ) := by
      field_simp [hpi_ne]
      ring
    have hdiv :
        (θ₀ + (m : ℝ) * (2 * Real.pi)) / (2 * Real.pi) - 1 / 2 =
          (2 * Real.pi * r + (2 * (d : ℝ) + 1) * Real.pi) / (2 * Real.pi) - 1 / 2 := by
      rw [hEq]
    rw [hLHS, hRHS] at hdiv
    have hfrac := congrArg Int.fract hdiv
    rw [Int.fract_add_intCast, Int.fract_add_intCast, hfr] at hfrac
    rw [← hfrac] at hr_not
    exact hr_not (Finset.mem_coe.mpr (Finset.mem_insert_self (f θ₀) S₁))

private lemma exists_root_Ioo_of_opposite_sign (Q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hsupp : (Q.eval a < 0 ∧ 0 < Q.eval b) ∨ (0 < Q.eval a ∧ Q.eval b < 0)) :
    ∃ r ∈ Set.Ioo a b, Q.eval r = 0 := by
  rcases hsupp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact intermediate_value_Ioo hab.le Q.continuousOn ⟨ha, hb⟩
  · exact intermediate_value_Ioo' hab.le Q.continuousOn ⟨hb, ha⟩

private lemma sq_sub_dvd_of_eval_and_deriv_eq_zero {G : Polynomial ℝ} {r : ℝ}
    (h0 : G.eval r = 0) (h1 : (derivative G).eval r = 0) :
    (X - C r) ^ 2 ∣ G := by
  have hdvd1 : X - C r ∣ G := Polynomial.dvd_iff_isRoot.mpr h0
  rcases hdvd1 with ⟨Q, rfl⟩
  have hderiv : derivative ((X - C r) * Q) = Q + (X - C r) * derivative Q := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have hQ0 : Q.eval r = 0 := by
    have hev := congrArg (eval r) hderiv
    rw [h1, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hev
    exact hev.symm
  have hdvd2 : X - C r ∣ Q := Polynomial.dvd_iff_isRoot.mpr hQ0
  rcases hdvd2 with ⟨Q₁, rfl⟩
  refine ⟨Q₁, by ring⟩

private lemma roots_alternate_contradiction {Q₁ : Polynomial ℝ} {n : ℕ} (hn : 1 ≤ n)
    {tNode : ℕ → ℝ} (ht_mono : StrictMonoOn tNode (Set.Iio (2 * n))) (hQ₁_ne : Q₁ ≠ 0)
    (hQ₁_deg : Q₁.natDegree ≤ 2 * n - 2)
    (hsupp : ∀ j < 2 * n - 1,
      (Q₁.eval (tNode j) < 0 ∧ 0 < Q₁.eval (tNode (j + 1))) ∨
      (0 < Q₁.eval (tNode j) ∧ Q₁.eval (tNode (j + 1)) < 0)) : False := by
  have hroots_step : ∀ j < 2 * n - 1,
      ∃ r ∈ Set.Ioo (tNode j) (tNode (j + 1)), Q₁.eval r = 0 := fun j hj =>
    exists_root_Ioo_of_opposite_sign Q₁
      (ht_mono (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (Nat.lt_succ_self j))
      (hsupp j hj)
  choose rNode hr_mem hr_eval using fun j : { j : ℕ // j < 2 * n - 1 } => hroots_step j.1 j.2
  let rFn : ℕ → ℝ := fun j => if hj : j < 2 * n - 1 then rNode ⟨j, hj⟩ else 0
  have hr_eq : ∀ {j : ℕ} (hj : j < 2 * n - 1), rFn j = rNode ⟨j, hj⟩ := fun hj => by
    simp only [rFn, hj, ↓reduceDIte]
  have hrFn_lt : ∀ {i j : ℕ} (hi : i < 2 * n - 1) (hj : j < 2 * n - 1) (hij : i < j),
      rFn i < rFn j := by
    intro i j hi hj hij
    rw [hr_eq hi, hr_eq hj]
    have hi_mem := hr_mem ⟨i, hi⟩
    have hj_mem := hr_mem ⟨j, hj⟩
    have hti1_le_tj : tNode (i + 1) ≤ tNode j := by
      by_cases heq : i + 1 = j
      · rw [heq]
      · exact (ht_mono (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega))
          (by omega)).le
    linarith [hi_mem.2, hj_mem.1]
  have hInj : Set.InjOn rFn (Finset.range (2 * n - 1)) := by
    intro i hi j hj heq
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact absurd heq (hrFn_lt hi' hj' hij).ne
    · rfl
    · exact absurd heq.symm (hrFn_lt hj' hi' hij).ne
  have hQ₁_zero : Q₁ = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.range (2 * n - 1)) hInj ?_ ?_
    · rw [Finset.card_range]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree
        (by exact_mod_cast (by omega : Q₁.natDegree < 2 * n - 1))
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [hr_eq hj']
      exact hr_eval ⟨j, hj'⟩
  exact hQ₁_ne hQ₁_zero

private lemma van_der_corput_schaake_one {P : Polynomial ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hdeg : P.natDegree ≤ n) (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1) (θ₀ : ℝ) :
    (n : ℝ) ^ 2 * (P.eval (Real.cos θ₀)) ^ 2 +
      ((derivative P).eval (Real.cos θ₀) * Real.sin θ₀) ^ 2 ≤ (n : ℝ) ^ 2 := by
  by_contra hlt
  push Not at hlt
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let a : ℝ := P.eval (Real.cos θ₀)
  let b : ℝ := (derivative P).eval (Real.cos θ₀) * Real.sin θ₀ / (n : ℝ)
  have hab_gt : 1 < a ^ 2 + b ^ 2 := by
    dsimp [a, b]
    have hmul : (n : ℝ) ^ 2 * 1 <
        (n : ℝ) ^ 2 * (P.eval (Real.cos θ₀) ^ 2 +
          ((derivative P).eval (Real.cos θ₀) * Real.sin θ₀ / (n : ℝ)) ^ 2) := by
      have heq : (n : ℝ) ^ 2 * (P.eval (Real.cos θ₀) ^ 2 +
          ((derivative P).eval (Real.cos θ₀) * Real.sin θ₀ / (n : ℝ)) ^ 2) =
          (n : ℝ) ^ 2 * P.eval (Real.cos θ₀) ^ 2 +
            ((derivative P).eval (Real.cos θ₀) * Real.sin θ₀) ^ 2 := by
        field_simp [hn_pos.ne']
      linarith
    exact lt_of_mul_lt_mul_left hmul (sq_nonneg (n : ℝ))
  let R : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hR_gt : 1 < R := (Real.lt_sqrt zero_le_one).mpr (by simpa using hab_gt)
  have hR_pos : 0 < R := lt_trans zero_lt_one hR_gt
  let c : ℝ := 1 / R
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hc_lt : c < 1 := by dsimp [c]; exact div_lt_one hR_pos |>.mpr hR_gt
  let z : ℂ := ⟨c * a, c * b⟩
  have hz_norm : ‖z‖ = 1 := by
    have hre_im : z.re * z.re + z.im * z.im = 1 := by
      dsimp [z, c, R]
      have hsq : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
      have hR_ne : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := hR_pos.ne'
      field_simp [hR_ne]
      nlinarith [hsq]
    have hnsq : Complex.normSq z = 1 := by simpa [Complex.normSq_apply] using hre_im
    have hsq_norm : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, hnsq]
    nlinarith [hsq_norm, norm_nonneg z]
  let α : ℝ := (n : ℝ) * θ₀ - Complex.arg z
  have hcos_α : Real.cos ((n : ℝ) * θ₀ - α) = c * a := by
    have heq : (n : ℝ) * θ₀ - α = Complex.arg z := by dsimp [α]; ring
    rw [heq]
    simpa [hz_norm, z] using Complex.norm_mul_cos_arg z
  have hsin_α : Real.sin ((n : ℝ) * θ₀ - α) = c * b := by
    have heq : (n : ℝ) * θ₀ - α = Complex.arg z := by dsimp [α]; ring
    rw [heq]
    simpa [hz_norm, z] using Complex.norm_mul_sin_arg z
  obtain ⟨β, hβ_nodes, hβ_star⟩ := choose_weierstrass_shift hn α θ₀
  let H : ℝ → ℝ := fun θ => Real.cos ((n : ℝ) * θ - α) - c * P.eval (Real.cos θ)
  let G : Polynomial ℝ :=
    C (Real.cos α) * weierstrassHomog β n (Chebyshev.T ℝ n) +
    C (Real.sin α) * (weierstrassHomog β (n - 1) (Chebyshev.U ℝ (n - 1 : ℕ)) * homogSin β) -
    C c * weierstrassHomog β n P
  have hG_deg : G.natDegree ≤ 2 * n := by
    dsimp [G]
    refine le_trans (natDegree_sub_le _ _) (max_le (le_trans (natDegree_add_le _ _) (max_le ?_ ?_)) ?_)
    · refine le_trans (natDegree_C_mul_le (Real.cos α) _) ?_
      exact natDegree_weierstrassHomog_le β n _
    · refine le_trans (natDegree_C_mul_le (Real.sin α) _) ?_
      refine le_trans natDegree_mul_le ?_
      have h1 := natDegree_weierstrassHomog_le β (n - 1) (Chebyshev.U ℝ (n - 1 : ℕ))
      have h2 := natDegree_homogSin_le β
      omega
    · refine le_trans (natDegree_C_mul_le c _) ?_
      exact natDegree_weierstrassHomog_le β n P
  have hG_eval : ∀ t : ℝ, G.eval t = (1 + t ^ 2) ^ n * H (β + 2 * Real.arctan t) := by
    intro t
    let θ := β + 2 * Real.arctan t
    have hTdeg : (Chebyshev.T ℝ n).natDegree ≤ n := by simp
    have hUdeg : (Chebyshev.U ℝ (n - 1 : ℕ)).natDegree ≤ n - 1 := by simp
    have hT_ev : (weierstrassHomog β n (Chebyshev.T ℝ n)).eval t =
        (1 + t ^ 2) ^ n * Real.cos ((n : ℝ) * θ) := by
      rw [eval_weierstrassHomog β n _ hTdeg t]
      exact congrArg ((1 + t ^ 2) ^ n * ·)
        (Polynomial.Chebyshev.T_real_cos (n := (n : ℤ)) (θ := θ))
    have hU_ev :
        (weierstrassHomog β (n - 1) (Chebyshev.U ℝ (n - 1 : ℕ))).eval t * (homogSin β).eval t =
          (1 + t ^ 2) ^ n * Real.sin ((n : ℝ) * θ) := by
      rw [eval_weierstrassHomog β (n - 1) _ hUdeg t]
      have hsin_eq := Polynomial.Chebyshev.U_real_cos (n := ((n - 1 : ℕ) : ℤ)) (θ := θ)
      have hcast : (((n - 1 : ℕ) : ℤ) + 1 : ℝ) = (n : ℝ) := by
        have h1 : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel hn
        exact_mod_cast h1
      rw [hcast] at hsin_eq
      have hden : 1 + t ^ 2 ≠ 0 := by positivity
      have hsinθ : (homogSin β).eval t = (1 + t ^ 2) * Real.sin θ := by
        rw [sin_weierstrass_eq]
        field_simp [hden]
      have hpow : (1 + t ^ 2) ^ (n - 1) * (1 + t ^ 2) = (1 + t ^ 2) ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      calc
        (1 + t ^ 2) ^ (n - 1) * (Chebyshev.U ℝ (n - 1 : ℕ)).eval (Real.cos θ) * (homogSin β).eval t
            = ((1 + t ^ 2) ^ (n - 1) * (1 + t ^ 2)) *
                ((Chebyshev.U ℝ (n - 1 : ℕ)).eval (Real.cos θ) * Real.sin θ) := by
              rw [hsinθ]; ring
        _ = (1 + t ^ 2) ^ n * Real.sin ((n : ℝ) * θ) := by rw [hpow, hsin_eq]
    have hP_ev : (weierstrassHomog β n P).eval t = (1 + t ^ 2) ^ n * P.eval (Real.cos θ) :=
      eval_weierstrassHomog β n P hdeg t
    dsimp [G, H]
    change (C (Real.cos α) * weierstrassHomog β n (Chebyshev.T ℝ n) +
        C (Real.sin α) * (weierstrassHomog β (n - 1) (Chebyshev.U ℝ (n - 1 : ℕ)) * homogSin β) -
        C c * weierstrassHomog β n P).eval t =
      (1 + t ^ 2) ^ n * (Real.cos ((n : ℝ) * θ - α) - c * P.eval (Real.cos θ))
    simp only [eval_sub, eval_add, eval_mul, eval_C]
    rw [hT_ev, hU_ev, hP_ev, Real.cos_sub ((n : ℝ) * θ) α]
    ring
  let q : ℤ := ⌊(θ₀ - (β - Real.pi)) / (2 * Real.pi)⌋
  let s_star : ℝ := θ₀ - (q : ℝ) * (2 * Real.pi)
  have hs_star_lo : β - Real.pi < s_star := by
    have hq_le : (q : ℝ) ≤ (θ₀ - (β - Real.pi)) / (2 * Real.pi) := Int.floor_le _
    have hle : β - Real.pi ≤ s_star := by
      dsimp [s_star]
      have hmul := mul_le_mul_of_nonneg_right hq_le (by positivity : 0 ≤ 2 * Real.pi)
      rw [div_mul_cancel₀ _ (by positivity)] at hmul
      linarith
    have hne : s_star ≠ β - Real.pi := by
      intro heq
      apply hβ_star (-q) (-1)
      push_cast
      dsimp [s_star] at heq
      linarith
    exact lt_of_le_of_ne hle hne.symm
  have hs_star_hi : s_star < β + Real.pi := by
    have hlt := Int.lt_floor_add_one ((θ₀ - (β - Real.pi)) / (2 * Real.pi))
    have hmul := mul_lt_mul_of_pos_right hlt (by positivity : 0 < 2 * Real.pi)
    rw [div_mul_cancel₀ _ (by positivity)] at hmul
    dsimp [s_star]
    linarith
  let t_star : ℝ := Real.tan ((s_star - β) / 2)
  have hθ_star : β + 2 * Real.arctan t_star = s_star := by
    dsimp [t_star]
    rw [Real.arctan_tan (by linarith) (by linarith)]
    ring
  have hcos_star : Real.cos s_star = Real.cos θ₀ := by
    dsimp [s_star]; rw [Real.cos_sub_int_mul_two_pi]
  have hsin_star : Real.sin s_star = Real.sin θ₀ := by
    dsimp [s_star]; rw [Real.sin_sub_int_mul_two_pi]
  have hcos_n_star : Real.cos ((n : ℝ) * s_star - α) = Real.cos ((n : ℝ) * θ₀ - α) := by
    have heq : (n : ℝ) * s_star - α =
        ((n : ℝ) * θ₀ - α) - (((n : ℤ) * q : ℤ) : ℝ) * (2 * Real.pi) := by
      dsimp [s_star]; push_cast; ring
    rw [heq, Real.cos_sub_int_mul_two_pi]
  have hsin_n_star : Real.sin ((n : ℝ) * s_star - α) = Real.sin ((n : ℝ) * θ₀ - α) := by
    have heq : (n : ℝ) * s_star - α =
        ((n : ℝ) * θ₀ - α) - (((n : ℤ) * q : ℤ) : ℝ) * (2 * Real.pi) := by
      dsimp [s_star]; push_cast; ring
    rw [heq, Real.sin_sub_int_mul_two_pi]
  have hH_star : H s_star = 0 := by
    dsimp [H]; rw [hcos_n_star, hcos_α, hcos_star]; dsimp [a]; ring
  have hH_deriv_star : HasDerivAt H 0 s_star := by
    have hin : HasDerivAt (fun θ : ℝ => (n : ℝ) * θ - α) (n : ℝ) s_star := by
      simpa using ((hasDerivAt_id s_star).const_mul (n : ℝ)).sub_const α
    have h1 : HasDerivAt (fun θ : ℝ => Real.cos ((n : ℝ) * θ - α))
        (-Real.sin ((n : ℝ) * s_star - α) * (n : ℝ)) s_star := by
      simpa [Function.comp_def] using (Real.hasDerivAt_cos ((n : ℝ) * s_star - α)).comp s_star hin
    have h2 : HasDerivAt (fun θ : ℝ => c * P.eval (Real.cos θ))
        (c * ((derivative P).eval (Real.cos s_star) * (-Real.sin s_star))) s_star := by
      have hp : HasDerivAt (fun θ : ℝ => P.eval (Real.cos θ))
          ((derivative P).eval (Real.cos s_star) * (-Real.sin s_star)) s_star := by
        simpa [Function.comp_def] using
          (P.hasDerivAt (Real.cos s_star)).comp s_star (Real.hasDerivAt_cos s_star)
      exact hp.const_mul c
    have hsub := h1.fun_sub h2
    have hzero : -Real.sin ((n : ℝ) * s_star - α) * (n : ℝ) -
        c * ((derivative P).eval (Real.cos s_star) * (-Real.sin s_star)) = 0 := by
      rw [hsin_n_star, hsin_α, hcos_star, hsin_star]
      dsimp [b]
      field_simp [hn_pos.ne']
      ring
    rwa [hzero] at hsub
  have hG_eval_star : G.eval t_star = 0 := by rw [hG_eval, hθ_star, hH_star, mul_zero]
  have hG_deriv_star : (derivative G).eval t_star = 0 := by
    have hd1 : HasDerivAt (fun t : ℝ => G.eval t) ((derivative G).eval t_star) t_star :=
      G.hasDerivAt t_star
    have hd_θ : HasDerivAt (fun t : ℝ => β + 2 * Real.arctan t)
        (2 * (1 / (1 + t_star ^ 2))) t_star :=
      ((Real.hasDerivAt_arctan t_star).const_mul 2).const_add β
    have hd_H : HasDerivAt (fun t : ℝ => H (β + 2 * Real.arctan t))
        (0 * (2 * (1 / (1 + t_star ^ 2)))) t_star := by
      have hH' : HasDerivAt H 0 (β + 2 * Real.arctan t_star) := by rwa [hθ_star]
      simpa [Function.comp_def] using HasDerivAt.comp t_star hH' hd_θ
    have hb : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t_star) t_star := by
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t_star) t_star := by
        simpa using (hasDerivAt_id t_star).fun_pow 2
      simpa using hsq.const_add (1 : ℝ)
    have hd_pow : HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ n)
        ((n : ℝ) * (1 + t_star ^ 2) ^ (n - 1) * (2 * t_star)) t_star :=
      hb.fun_pow n
    have hd2 : HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ n * H (β + 2 * Real.arctan t))
        ((n : ℝ) * (1 + t_star ^ 2) ^ (n - 1) * (2 * t_star) * H s_star +
          (1 + t_star ^ 2) ^ n * (0 * (2 * (1 / (1 + t_star ^ 2))))) t_star := by
      simpa [hθ_star] using hd_pow.fun_mul hd_H
    have hd2_zero : HasDerivAt (fun t : ℝ => G.eval t) 0 t_star := by
      have h0d : (n : ℝ) * (1 + t_star ^ 2) ^ (n - 1) * (2 * t_star) * H s_star +
          (1 + t_star ^ 2) ^ n * (0 * (2 * (1 / (1 + t_star ^ 2)))) = 0 := by
        rw [hH_star]; ring
      rw [h0d] at hd2
      exact hd2.congr_of_eventuallyEq (Filter.Eventually.of_forall hG_eval)
    exact hd1.unique hd2_zero
  obtain ⟨Q₁, hG_fac⟩ := sq_sub_dvd_of_eval_and_deriv_eq_zero hG_eval_star hG_deriv_star
  let k₀ : ℤ := ⌊((n : ℝ) * (β - Real.pi) - α) / Real.pi⌋ + 1
  let sNode : ℕ → ℝ := fun j => (α + ((k₀ + (j : ℤ) : ℤ) : ℝ) * Real.pi) / (n : ℝ)
  let tNode : ℕ → ℝ := fun j => Real.tan ((sNode j - β) / 2)
  have hsNode_strictMono : StrictMono sNode := by
    intro i j hij
    dsimp [sNode]
    have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    push_cast
    exact div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hn_pos
  have hsNode_bounds : ∀ j < 2 * n, β - Real.pi < sNode j ∧ sNode j < β + Real.pi := by
    intro j hj
    dsimp [sNode]
    have hk0_gt : ((n : ℝ) * (β - Real.pi) - α) / Real.pi < (k₀ : ℝ) := by
      dsimp [k₀]; push_cast; exact Int.lt_floor_add_one _
    have hk0_le : ((k₀ - 1 : ℤ) : ℝ) ≤ ((n : ℝ) * (β - Real.pi) - α) / Real.pi := by
      dsimp [k₀]; push_cast
      linarith [Int.floor_le (((n : ℝ) * (β - Real.pi) - α) / Real.pi)]
    have hlo : β - Real.pi < (α + ((k₀ + (j : ℤ) : ℤ) : ℝ) * Real.pi) / (n : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hk0_gt Real.pi_pos
      rw [div_mul_cancel₀ _ Real.pi_ne_zero] at hmul
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hnum : (β - Real.pi) * (n : ℝ) < α + ((k₀ + (j : ℤ) : ℤ) : ℝ) * Real.pi := by
        push_cast; nlinarith [Real.pi_pos]
      exact (lt_div_iff₀ hn_pos).mpr hnum
    have hhi_le : (α + ((k₀ + (j : ℤ) : ℤ) : ℝ) * Real.pi) / (n : ℝ) ≤ β + Real.pi := by
      have hmul := mul_le_mul_of_nonneg_right hk0_le Real.pi_pos.le
      rw [div_mul_cancel₀ _ Real.pi_ne_zero] at hmul
      have hj_le : (j : ℝ) ≤ 2 * (n : ℝ) - 1 := by
        have h' : (j : ℝ) + 1 ≤ 2 * (n : ℝ) := by exact_mod_cast (show j + 1 ≤ 2 * n from hj)
        linarith
      have hnum : α + ((k₀ + (j : ℤ) : ℤ) : ℝ) * Real.pi ≤ (β + Real.pi) * (n : ℝ) := by
        push_cast at hmul ⊢; nlinarith [Real.pi_pos]
      exact (div_le_iff₀ hn_pos).mpr hnum
    have hne : (α + ((k₀ + (j : ℤ) : ℤ) : ℝ) * Real.pi) / (n : ℝ) ≠ β + Real.pi := by
      have := hβ_nodes (k₀ + (j : ℤ)) 0
      simpa using this
    exact ⟨hlo, lt_of_le_of_ne hhi_le hne⟩
  have htNode_strictMono : StrictMonoOn tNode (Set.Iio (2 * n)) := by
    intro i hi j hj hij
    dsimp [tNode]
    refine Real.strictMonoOn_tan ?_ ?_ ?_
    · have hiB := hsNode_bounds i hi; exact ⟨by linarith, by linarith⟩
    · have hjB := hsNode_bounds j hj; exact ⟨by linarith, by linarith⟩
    · linarith [hsNode_strictMono hij]
  have hθ_node : ∀ j < 2 * n, β + 2 * Real.arctan (tNode j) = sNode j := by
    intro j hj
    have hjB := hsNode_bounds j hj
    dsimp [tNode]
    rw [Real.arctan_tan (by linarith) (by linarith)]
    ring
  have hG_sign : ∀ j < 2 * n,
      (Even (k₀ + (j : ℤ)) → 0 < G.eval (tNode j)) ∧
      (Odd (k₀ + (j : ℤ)) → G.eval (tNode j) < 0) := by
    intro j hj
    have hcos_arg :
        Real.cos ((n : ℝ) * sNode j - α) = Real.cos (((k₀ + (j : ℤ) : ℤ) : ℝ) * Real.pi) := by
      congr 1; dsimp [sNode]; field_simp [hn_pos.ne']; ring
    have hP_abs : |P.eval (Real.cos (sNode j))| ≤ 1 := hbounded _ (Real.cos_mem_Icc _)
    let v : ℝ := P.eval (Real.cos (sNode j))
    have hv_lo : -1 ≤ v := (abs_le.mp hP_abs).1
    have hv_hi : v ≤ 1 := (abs_le.mp hP_abs).2
    have hcv_hi : c * v ≤ c := by simpa using mul_le_mul_of_nonneg_left hv_hi hc_pos.le
    have hcv_lo : -c ≤ c * v := by simpa using mul_le_mul_of_nonneg_left hv_lo hc_pos.le
    have hpow_pos : 0 < (1 + (tNode j) ^ 2) ^ n := by positivity
    rw [hG_eval, hθ_node j hj]
    dsimp [H]
    rw [hcos_arg, Real.cos_int_mul_pi]
    constructor
    · intro hev
      rw [hev.neg_one_zpow]
      have hH_pos : 0 < 1 - c * P.eval (Real.cos (sNode j)) := by
        change 0 < 1 - c * v
        linarith [hcv_hi]
      exact mul_pos hpow_pos hH_pos
    · intro hodd
      rw [hodd.neg_one_zpow]
      have hH_neg : -1 - c * P.eval (Real.cos (sNode j)) < 0 := by
        change -1 - c * v < 0
        linarith [hcv_lo]
      exact mul_neg_of_pos_of_neg hpow_pos hH_neg
  have hG_ne_zero : ∀ j < 2 * n, G.eval (tNode j) ≠ 0 := by
    intro j hj h0
    rcases Int.even_or_odd (k₀ + (j : ℤ)) with hev | hodd
    · exact (hG_sign j hj).1 hev |>.ne' h0
    · exact (hG_sign j hj).2 hodd |>.ne h0
  have hQ₁_ne : Q₁ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hG_fac
    have := hG_ne_zero 0 (by omega)
    rw [hG_fac, eval_zero] at this
    exact this rfl
  have hQ₁_deg : Q₁.natDegree ≤ 2 * n - 2 := by
    have hsq_ne : (X - C t_star) ^ 2 ≠ 0 := pow_ne_zero 2 (X_sub_C_ne_zero t_star)
    have hmul_deg := natDegree_mul hsq_ne hQ₁_ne
    rw [← hG_fac] at hmul_deg
    have hsq_deg : ((X - C t_star) ^ 2).natDegree = 2 := by simp [natDegree_pow]
    omega
  have hQ₁_sign : ∀ j < 2 * n,
      (Even (k₀ + (j : ℤ)) → 0 < Q₁.eval (tNode j)) ∧
      (Odd (k₀ + (j : ℤ)) → Q₁.eval (tNode j) < 0) := by
    intro j hj
    have hfac_eval : G.eval (tNode j) = (tNode j - t_star) ^ 2 * Q₁.eval (tNode j) := by
      conv_lhs => rw [hG_fac]
      simp
    have hsq_pos : 0 < (tNode j - t_star) ^ 2 := by
      refine sq_pos_iff.mpr (sub_ne_zero.mpr fun heq => ?_)
      have h0 := hG_ne_zero j hj
      rw [heq, hG_eval_star] at h0
      exact h0 rfl
    constructor
    · intro hev
      have hpos := (hG_sign j hj).1 hev
      rw [hfac_eval] at hpos
      exact (pos_iff_pos_of_mul_pos hpos).mp hsq_pos
    · intro hodd
      have hneg := (hG_sign j hj).2 hodd
      rw [hfac_eval] at hneg
      exact (mul_neg_iff.mp hneg).elim (fun ⟨_, hh⟩ => hh) (fun ⟨hh, _⟩ => absurd hh hsq_pos.asymm)
  refine roots_alternate_contradiction hn htNode_strictMono hQ₁_ne hQ₁_deg fun j hj => ?_
  rcases Int.even_or_odd (k₀ + (j : ℤ)) with hev | hodd
  · right
    have hodd1 : Odd (k₀ + ((j + 1 : ℕ) : ℤ)) := by
      push_cast
      rw [show k₀ + ((j : ℤ) + 1) = (k₀ + (j : ℤ)) + 1 by ring]
      exact hev.add_one
    exact ⟨(hQ₁_sign j (by omega)).1 hev, (hQ₁_sign (j + 1) (by omega)).2 hodd1⟩
  · left
    have hev1 : Even (k₀ + ((j + 1 : ℕ) : ℤ)) := by
      push_cast
      rw [show k₀ + ((j : ℤ) + 1) = (k₀ + (j : ℤ)) + 1 by ring]
      exact hodd.add_one
    exact ⟨(hQ₁_sign j (by omega)).2 hodd, (hQ₁_sign (j + 1) (by omega)).1 hev1⟩

/-- **Bernstein / Van der Corput–Schaake Inequality:**
for every polynomial `P : Polynomial ℝ` of degree at most `n` with `|P(t)| ≤ B` on
`[-1, 1]` (`0 ≤ B`), and every `θ : ℝ`,
  `n^2 * P(cos θ)^2 + (P'(cos θ) * sin θ)^2 ≤ n^2 * B^2`. -/
theorem van_der_corput_schaake (P : Polynomial ℝ) (n : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B) (θ : ℝ) :
    (n : ℝ) ^ 2 * (P.eval (Real.cos θ)) ^ 2 +
      ((derivative P).eval (Real.cos θ) * Real.sin θ) ^ 2 ≤ (n : ℝ) ^ 2 * B ^ 2 := by
  by_cases hn0 : n = 0
  · subst hn0
    have hP0 : P.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
    have hd0 : derivative P = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hP0, derivative_C]
    simp [hd0]
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    by_cases hB0 : B = 0
    · subst hB0
      rw [eq_zero_of_abs_le_zero_on_Icc hdeg hbounded]
      simp
    · have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      let Q : Polynomial ℝ := C B⁻¹ * P
      have hQdeg : Q.natDegree ≤ n := le_trans (natDegree_C_mul_le B⁻¹ P) hdeg
      have hQb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Q.eval t| ≤ 1 := by
        intro t ht
        dsimp [Q]
        rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hB_pos)]
        calc
          B⁻¹ * |P.eval t| ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hbounded t ht) (inv_nonneg.mpr hB)
          _ = 1 := inv_mul_cancel₀ hB0
      have hQ := van_der_corput_schaake_one hn1 hQdeg hQb θ
      dsimp [Q] at hQ
      rw [derivative_C_mul, eval_mul, eval_mul, eval_C] at hQ
      have hfac :
          (n : ℝ) ^ 2 * (B⁻¹ * P.eval (Real.cos θ)) ^ 2 +
              (B⁻¹ * (derivative P).eval (Real.cos θ) * Real.sin θ) ^ 2 =
            (B⁻¹) ^ 2 * ((n : ℝ) ^ 2 * P.eval (Real.cos θ) ^ 2 +
              ((derivative P).eval (Real.cos θ) * Real.sin θ) ^ 2) := by
        ring
      rw [hfac] at hQ
      have hmul := mul_le_mul_of_nonneg_left hQ (sq_nonneg B)
      calc
        (n : ℝ) ^ 2 * P.eval (Real.cos θ) ^ 2 +
            ((derivative P).eval (Real.cos θ) * Real.sin θ) ^ 2
            = B ^ 2 * ((B⁻¹) ^ 2 * ((n : ℝ) ^ 2 * P.eval (Real.cos θ) ^ 2 +
                ((derivative P).eval (Real.cos θ) * Real.sin θ) ^ 2)) := by
              field_simp [hB0]
        _ ≤ B ^ 2 * (n : ℝ) ^ 2 := hmul
        _ = (n : ℝ) ^ 2 * B ^ 2 := mul_comm _ _

end BernsteinVanDerCorputSchaake

section MarkovInterior

private lemma markov_deg_le_one {P : Polynomial ℝ} {B : ℝ}
    (hdeg : P.natDegree ≤ 1)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B) (x : ℝ) :
    |(derivative P).eval x| ≤ (1 : ℝ) ^ 2 * B := by
  have hddeg : (derivative P).natDegree = 0 :=
    Nat.eq_zero_of_le_zero (by have := Polynomial.natDegree_derivative_le (p := P); omega)
  have hderiv_const : derivative P = C ((derivative P).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hddeg
  have hderiv_ev : (derivative P).eval x = P.coeff 1 := by
    rw [hderiv_const, eval_C, Polynomial.coeff_derivative]
    simp
  have hev1 : P.eval 1 = P.coeff 0 + P.coeff 1 := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_range_succ,
      Finset.sum_range_one]
    norm_num
  have hevm1 : P.eval (-1) = P.coeff 0 - P.coeff 1 := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_range_succ,
      Finset.sum_range_one]
    norm_num
    ring
  have h1 : |P.eval 1| ≤ B := hbounded 1 ⟨by norm_num, by norm_num⟩
  have hm1 : |P.eval (-1)| ≤ B := hbounded (-1) ⟨by norm_num, by norm_num⟩
  have hdiff : P.eval 1 - P.eval (-1) = 2 * P.coeff 1 := by rw [hev1, hevm1]; ring
  rw [hderiv_ev, one_pow, one_mul]
  have h2 : 2 * |P.coeff 1| ≤ 2 * B := by
    calc
      2 * |P.coeff 1| = |2| * |P.coeff 1| := by norm_num
      _ = |2 * P.coeff 1| := (abs_mul 2 (P.coeff 1)).symm
      _ = |P.eval 1 - P.eval (-1)| := by rw [hdiff]
      _ ≤ |P.eval 1| + |P.eval (-1)| := abs_sub _ _
      _ ≤ B + B := add_le_add h1 hm1
      _ = 2 * B := by ring
  linarith

/-- **A. A. Markov's Interior Derivative Inequality (1889):**
if `P : Polynomial ℝ` has `P.natDegree ≤ n` and `|P.eval t| ≤ B` for all
`t ∈ [-1, 1]` (`0 ≤ B`), then for every `x ∈ [-1, 1]`,
  `|(Polynomial.derivative P).eval x| ≤ (n : ℝ) ^ 2 * B`. -/
theorem markov_interior_derivative_abs_le (P : Polynomial ℝ) (n : ℕ) {B x : ℝ}
    (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(derivative P).eval x| ≤ (n : ℝ) ^ 2 * B := by
  rcases Nat.lt_trichotomy n 1 with hn0 | rfl | hn2
  · have hn0' : n = 0 := Nat.lt_one_iff.mp hn0
    subst hn0'
    have hP0 : P.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
    have hd0 : derivative P = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hP0, derivative_C]
    simp [hd0]
  · simpa using markov_deg_le_one hdeg hbounded x
  · have hn2' : 2 ≤ n := hn2
    let δ : ℝ := Real.sqrt (1 - 1 / (n : ℝ) ^ 2)
    by_cases hx_right : δ ≤ x
    · exact markov_near_endpoint_right hn2' P hB hdeg hbounded hx_right hx.2
    · by_cases hx_left : x ≤ -δ
      · let Q : Polynomial ℝ := P.comp (-Polynomial.X)
        have hQdeg : Q.natDegree ≤ n := le_trans (natDegree_comp_neg_X P) hdeg
        have hQb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Q.eval t| ≤ B := by
          intro t ht
          dsimp [Q]
          rw [eval_comp, eval_neg, eval_X]
          exact hbounded (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        have hQ := markov_near_endpoint_right hn2' Q hB hQdeg hQb (x := -x)
          (by linarith) (by linarith [hx.1])
        dsimp [Q] at hQ
        rw [deriv_neg_X_comp P (-x), neg_neg, abs_neg] at hQ
        exact hQ
      · push Not at hx_right hx_left
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hrad_nn : 0 ≤ 1 - 1 / (n : ℝ) ^ 2 := by
          have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
            have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2'
            nlinarith
          have hdiv : 1 / (n : ℝ) ^ 2 ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
          linarith
        have hx_sq_lt : x ^ 2 < 1 - 1 / (n : ℝ) ^ 2 := by
          have habs_lt : |x| < δ := abs_lt.mpr ⟨hx_left, hx_right⟩
          have hsq := pow_lt_pow_left₀ habs_lt (abs_nonneg x) (by norm_num : 2 ≠ 0)
          rw [sq_abs] at hsq
          have hδsq : δ ^ 2 = 1 - 1 / (n : ℝ) ^ 2 := Real.sq_sqrt hrad_nn
          linarith
        have h1x_gt : 1 / (n : ℝ) ^ 2 ≤ 1 - x ^ 2 := by linarith
        let θ : ℝ := Real.arccos x
        have hcos : Real.cos θ = x := Real.cos_arccos hx.1 hx.2
        have hsin_sq : (Real.sin θ) ^ 2 = 1 - x ^ 2 := by
          have := Real.sin_sq_add_cos_sq θ
          rw [hcos] at this
          linarith
        have hvd := van_der_corput_schaake P n hB hdeg hbounded θ
        rw [hcos] at hvd
        have hmid : ((derivative P).eval x) ^ 2 * (1 - x ^ 2) ≤ (n : ℝ) ^ 2 * B ^ 2 := by
          have hmul : ((derivative P).eval x) ^ 2 * (1 - x ^ 2) =
              ((derivative P).eval x * Real.sin θ) ^ 2 := by
            rw [mul_pow, hsin_sq]
          have hsq_nn : 0 ≤ (n : ℝ) ^ 2 * (P.eval x) ^ 2 := by positivity
          linarith [hmul, hvd]
        have hinv_le : ((derivative P).eval x) ^ 2 * (1 / (n : ℝ) ^ 2) ≤ (n : ℝ) ^ 2 * B ^ 2 := by
          have hle1 : ((derivative P).eval x) ^ 2 * (1 / (n : ℝ) ^ 2) ≤
              ((derivative P).eval x) ^ 2 * (1 - x ^ 2) :=
            mul_le_mul_of_nonneg_left h1x_gt (sq_nonneg _)
          linarith
        have hsq_bound : ((derivative P).eval x) ^ 2 ≤ ((n : ℝ) ^ 2 * B) ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_right hinv_le (sq_nonneg (n : ℝ))
          calc
            ((derivative P).eval x) ^ 2
                = ((derivative P).eval x) ^ 2 * (1 / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
                  field_simp [hn_pos.ne']
            _ ≤ ((n : ℝ) ^ 2 * B ^ 2) * (n : ℝ) ^ 2 := hmul
            _ = ((n : ℝ) ^ 2 * B) ^ 2 := by ring
        have hrhs_nn : 0 ≤ (n : ℝ) ^ 2 * B := by positivity
        exact abs_le.mpr (abs_le_of_sq_le_sq' hsq_bound hrhs_nn)

/-- **Iterated Interior Markov Inequality:**
for every `s : ℕ` and `x ∈ [-1, 1]`,
  `|(derivative^[s] P).eval x| ≤ (∏ j ∈ Finset.range s, (((n - j : ℕ) : ℝ) ^ 2)) * B`. -/
theorem markov_iterate_derivative_interior_le (P : Polynomial ℝ) (n s : ℕ) {B x : ℝ}
    (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(derivative^[s] P).eval x| ≤
      (∏ j ∈ Finset.range s, (((n - j : ℕ) : ℝ) ^ 2)) * B := by
  induction s generalizing x with
  | zero =>
      simp only [Function.iterate_zero_apply, Finset.range_zero, Finset.prod_empty, one_mul]
      exact hbounded x hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hk_nn : 0 ≤ (∏ j ∈ Finset.range k, (((n - j : ℕ) : ℝ) ^ 2)) * B :=
        mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _) hB
      have hdeg_k : (derivative^[k] P).natDegree ≤ n - k :=
        le_trans (natDegree_iterate_derivative_le P k) (Nat.sub_le_sub_right hdeg k)
      have hstep := markov_interior_derivative_abs_le (derivative^[k] P) (n - k) hk_nn hdeg_k
        (fun t ht => ih ht) hx
      rw [Finset.prod_range_succ, mul_assoc]
      calc
        |(derivative (derivative^[k] P)).eval x|
            ≤ ((n - k : ℕ) : ℝ) ^ 2 *
                ((∏ j ∈ Finset.range k, (((n - j : ℕ) : ℝ) ^ 2)) * B) := hstep
        _ = (∏ j ∈ Finset.range k, (((n - j : ℕ) : ℝ) ^ 2)) *
              (((n - k : ℕ) : ℝ) ^ 2 * B) := by ring

/-- **Interior Markov Interval Transport to `[0, 1 / (L * m)]`:**
under the reciprocal-grid hypothesis `|P(t)| ≤ B` on `[0, 1 / (L * m)]` (`0 < L`, `1 ≤ m`,
`deg P ≤ m`), every `s`-th derivative satisfies
  `|(P^(s))(t)| ≤ (2 * L * m)^s * (∏ j ∈ Finset.range s, (((m - j : ℕ) : ℝ)^2)) * B`
for all `t ∈ [0, 1 / (L * m)]`. -/
theorem markov_interior_interval_transfer (P : Polynomial ℝ) (m s : ℕ) {L B t : ℝ}
    (hL : 0 < L) (hm : 1 ≤ m) (hB : 0 ≤ B) (hdeg : P.natDegree ≤ m)
    (hbounded : ∀ u ∈ Set.Icc (0 : ℝ) (1 / (L * (m : ℝ))), |P.eval u| ≤ B)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / (L * (m : ℝ)))) :
    |(derivative^[s] P).eval t| ≤
      (2 * L * (m : ℝ)) ^ s *
        (∏ j ∈ Finset.range s, (((m - j : ℕ) : ℝ) ^ 2)) * B := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hLm_pos : 0 < L * (m : ℝ) := mul_pos hL hm_pos
  let δ : ℝ := 1 / (2 * L * (m : ℝ))
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have h2δ : 2 * δ = 1 / (L * (m : ℝ)) := by
    dsimp [δ]
    field_simp [hLm_pos.ne']
  let Q : Polynomial ℝ := P.comp (C δ * X + C δ)
  have hQdeg : Q.natDegree ≤ m := by
    dsimp [Q]
    refine le_trans natDegree_comp_le ?_
    have hlin : (C δ * X + C δ : Polynomial ℝ).natDegree ≤ 1 := by
      refine le_trans (natDegree_add_le _ _) (max_le ?_ (by simp))
      exact le_trans (natDegree_C_mul_le δ X) (by simp)
    exact le_trans (Nat.mul_le_mul_left _ hlin) (by simpa using hdeg)
  have hQb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |Q.eval u| ≤ B := by
    intro u hu
    dsimp [Q]
    rw [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    refine hbounded (δ * u + δ) ⟨by nlinarith [hu.1, hδ_pos], ?_⟩
    rw [← h2δ]
    nlinarith [hu.2, hδ_pos]
  let x : ℝ := t / δ - 1
  have hx_mem : x ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp [x]
    have ht0 : 0 ≤ t / δ := div_nonneg ht.1 hδ_pos.le
    have ht2 : t / δ ≤ 2 := by
      rw [div_le_iff₀ hδ_pos]
      have hmul : 2 * δ = 1 / (L * (m : ℝ)) := h2δ
      linarith [ht.2]
    exact ⟨by linarith, by linarith⟩
  have hQ_int := markov_iterate_derivative_interior_le Q m s hB hQdeg hQb hx_mem
  have hQ_eval := iterate_derivative_affine_eval P δ δ x s
  have htx : δ * x + δ = t := by
    dsimp [x]
    field_simp [hδ_pos.ne']
    ring
  change (derivative^[s] Q).eval x = δ ^ s * (derivative^[s] P).eval (δ * x + δ) at hQ_eval
  rw [htx] at hQ_eval
  rw [hQ_eval, abs_mul, abs_of_pos (pow_pos hδ_pos s)] at hQ_int
  have hpow_pos : 0 < δ ^ s := pow_pos hδ_pos s
  have hinv_eq : (δ ^ s)⁻¹ = (2 * L * (m : ℝ)) ^ s := by
    dsimp [δ]
    rw [one_div, inv_pow, inv_inv]
  have hle := mul_le_mul_of_nonneg_left hQ_int (inv_nonneg.mpr hpow_pos.le)
  calc
    |(derivative^[s] P).eval t|
        = (δ ^ s)⁻¹ * (δ ^ s * |(derivative^[s] P).eval t|) := by
          field_simp [hpow_pos.ne']
    _ ≤ (δ ^ s)⁻¹ * ((∏ j ∈ Finset.range s, (((m - j : ℕ) : ℝ) ^ 2)) * B) := hle
    _ = (2 * L * (m : ℝ)) ^ s *
          (∏ j ∈ Finset.range s, (((m - j : ℕ) : ℝ) ^ 2)) * B := by
          rw [hinv_eq]
          ring

end MarkovInterior

end Mathematics212
