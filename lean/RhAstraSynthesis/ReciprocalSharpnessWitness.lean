import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic

/-!
# Extremal reciprocal-grid witness for cubic derivative growth

Constructs the explicit family of polynomials
  `P_{k,ℓ}(t) = (∏_{j=1}^k (1 - j*t)) * T_ℓ(1 - 2*k*t)`
of degree at most `k + ℓ`, uniformly bounded by `1` on the entire reciprocal
lattice `{1/n : n ≥ 1}`, yet satisfying
  `|P_{k,ℓ}'(0)| = k(k+1)/2 + 2 k ℓ^2`.
Setting `k = ℓ = m` gives `deg P_{m,m} ≤ 2m` and `|P_{m,m}'(0)| = 2 m^3 + m(m+1)/2 ≥ 2 m^3 > m^2`,
showing why reciprocal-grid Markov bounds grow at cubic order without a Remez
continuous-interval supremum reduction.
-/

namespace RhAstraSynthesis

open Polynomial Finset

/-- The reciprocal-grid annihilator polynomial `∏_{j=1}^k (1 - j*X)`. -/
noncomputable def reciprocalAnnihilator (k : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.Icc 1 k, (1 - Polynomial.C (j : ℝ) * Polynomial.X)

/-- The shifted Chebyshev extremal factor `T_ℓ(1 - 2*k*X)` on `[0, 1/k]`. -/
noncomputable def shiftedChebyshevFactor (k l : ℕ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ (l : ℤ)).comp (1 - Polynomial.C (2 * (k : ℝ)) * Polynomial.X)

/-- The composite witness `P_{k,ℓ}(t) = (∏_{j=1}^k (1 - j*t)) * T_ℓ(1 - 2*k*t)`. -/
noncomputable def reciprocalSharpnessWitness (k l : ℕ) : Polynomial ℝ :=
  reciprocalAnnihilator k * shiftedChebyshevFactor k l

theorem reciprocalAnnihilator_natDegree_le (k : ℕ) :
    (reciprocalAnnihilator k).natDegree ≤ k := by
  unfold reciprocalAnnihilator
  calc
    (∏ j ∈ Finset.Icc 1 k, (1 - Polynomial.C (j : ℝ) * Polynomial.X)).natDegree
        ≤ ∑ j ∈ Finset.Icc 1 k, (1 - Polynomial.C (j : ℝ) * Polynomial.X).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 k, 1 := by
      apply Finset.sum_le_sum
      intro j _
      calc
        (1 - Polynomial.C (j : ℝ) * Polynomial.X).natDegree
            ≤ max (1 : Polynomial ℝ).natDegree (Polynomial.C (j : ℝ) * Polynomial.X).natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ ≤ 1 := by
          simp only [Polynomial.natDegree_one, max_le_iff, zero_le, true_and]
          exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    _ = k := by simp

theorem shiftedChebyshevFactor_natDegree_le (k l : ℕ) :
    (shiftedChebyshevFactor k l).natDegree ≤ l := by
  unfold shiftedChebyshevFactor
  calc
    ((Polynomial.Chebyshev.T ℝ (l : ℤ)).comp
        (1 - Polynomial.C (2 * (k : ℝ)) * Polynomial.X)).natDegree
        ≤ (Polynomial.Chebyshev.T ℝ (l : ℤ)).natDegree *
            (1 - Polynomial.C (2 * (k : ℝ)) * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ l * 1 := by
      apply Nat.mul_le_mul
      · rw [Polynomial.Chebyshev.natDegree_T]
        exact Int.natAbs_natCast l |>.le
      · calc
          (1 - Polynomial.C (2 * (k : ℝ)) * Polynomial.X).natDegree
              ≤ max (1 : Polynomial ℝ).natDegree
                  (Polynomial.C (2 * (k : ℝ)) * Polynomial.X).natDegree :=
            Polynomial.natDegree_sub_le _ _
          _ ≤ 1 := by
            simp only [Polynomial.natDegree_one, max_le_iff, zero_le, true_and]
            exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    _ = l := Nat.mul_one l

theorem reciprocalSharpnessWitness_natDegree_le (k l : ℕ) :
    (reciprocalSharpnessWitness k l).natDegree ≤ k + l := by
  unfold reciprocalSharpnessWitness
  exact (Polynomial.natDegree_mul_le).trans
    (Nat.add_le_add (reciprocalAnnihilator_natDegree_le k)
      (shiftedChebyshevFactor_natDegree_le k l))

theorem reciprocalAnnihilator_eval (k : ℕ) (t : ℝ) :
    (reciprocalAnnihilator k).eval t = ∏ j ∈ Finset.Icc 1 k, (1 - (j : ℝ) * t) := by
  unfold reciprocalAnnihilator
  simp [Polynomial.eval_prod]

theorem reciprocalAnnihilator_eval_zero (k : ℕ) :
    (reciprocalAnnihilator k).eval 0 = 1 := by
  simp [reciprocalAnnihilator_eval]

theorem shiftedChebyshevFactor_eval_zero (k l : ℕ) :
    (shiftedChebyshevFactor k l).eval 0 = 1 := by
  unfold shiftedChebyshevFactor
  simp [Polynomial.eval_comp, Polynomial.Chebyshev.T_eval_one]

theorem reciprocalAnnihilator_eval_reciprocal_zero_of_le
    {k n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) :
    (reciprocalAnnihilator k).eval (1 / (n : ℝ)) = 0 := by
  rw [reciprocalAnnihilator_eval]
  apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hn1, hnk⟩)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem finset_prod_abs_le_one {s : Finset ℕ} {g : ℕ → ℝ}
    (hg : ∀ j ∈ s, |g j| ≤ 1) : ∏ j ∈ s, |g j| ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have ha1 : |g a| ≤ 1 := hg a (Finset.mem_insert_self a s)
      have hs1 : ∏ j ∈ s, |g j| ≤ 1 := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      have hs0 : 0 ≤ ∏ j ∈ s, |g j| := Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      calc
        |g a| * ∏ j ∈ s, |g j| ≤ 1 * ∏ j ∈ s, |g j| := mul_le_mul_of_nonneg_right ha1 hs0
        _ ≤ 1 := by linarith

theorem reciprocalAnnihilator_eval_reciprocal_abs_le_one
    (k n : ℕ) (hn : 1 ≤ n) :
    |(reciprocalAnnihilator k).eval (1 / (n : ℝ))| ≤ 1 := by
  by_cases hnk : n ≤ k
  · rw [reciprocalAnnihilator_eval_reciprocal_zero_of_le hn hnk, abs_zero]
    exact zero_le_one
  · have hkn : k < n := Nat.lt_of_not_ge hnk
    rw [reciprocalAnnihilator_eval, Finset.abs_prod]
    apply finset_prod_abs_le_one
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (hjk.trans hkn.le)
    have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hdiv_nonneg : 0 ≤ (j : ℝ) / (n : ℝ) := div_nonneg hj0 hn0.le
    have hdiv_le : (j : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn0).2 hjn
    have hfactor : 1 - (j : ℝ) * (1 / (n : ℝ)) = 1 - (j : ℝ) / (n : ℝ) := by ring
    rw [hfactor, abs_of_nonneg (by linarith)]
    linarith

theorem chebyshev_eval_abs_le_one (l : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ (l : ℤ)).eval y| ≤ 1 := by
  have hcos : Real.cos (Real.arccos y) = y := Real.cos_arccos hy.1 hy.2
  rw [← hcos, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem shiftedChebyshev_mem_Icc {k n : ℕ} (hk : k < n) :
    (1 - 2 * (k : ℝ) * (1 / (n : ℝ))) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  constructor
  · have : 2 * (k : ℝ) / (n : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hn0]
      linarith
    linarith [show 2 * (k : ℝ) * (1 / (n : ℝ)) = 2 * (k : ℝ) / (n : ℝ) by ring]
  · have : 0 ≤ 2 * (k : ℝ) * (1 / (n : ℝ)) := by positivity
    linarith

theorem reciprocalSharpnessWitness_eval_reciprocal_abs_le_one
    (k l n : ℕ) (hn : 1 ≤ n) :
    |(reciprocalSharpnessWitness k l).eval (1 / (n : ℝ))| ≤ 1 := by
  unfold reciprocalSharpnessWitness
  rw [Polynomial.eval_mul, abs_mul]
  by_cases hnk : n ≤ k
  · rw [reciprocalAnnihilator_eval_reciprocal_zero_of_le hn hnk, abs_zero, zero_mul]
    exact zero_le_one
  · have hkn : k < n := Nat.lt_of_not_ge hnk
    have h1 := reciprocalAnnihilator_eval_reciprocal_abs_le_one k n hn
    have hcheb :
        |(shiftedChebyshevFactor k l).eval (1 / (n : ℝ))| ≤ 1 := by
      unfold shiftedChebyshevFactor
      rw [Polynomial.eval_comp]
      have hev :
          (1 - Polynomial.C (2 * (k : ℝ)) * Polynomial.X).eval (1 / (n : ℝ)) =
            1 - 2 * (k : ℝ) * (1 / (n : ℝ)) := by
        simp
      rw [hev]
      exact chebyshev_eval_abs_le_one l (shiftedChebyshev_mem_Icc hkn)
    simpa only [one_mul] using mul_le_mul h1 hcheb (abs_nonneg _) zero_le_one

private theorem eval_derivative_prod_at_zero {ι : Type*} (s : Finset ι)
    (g : ι → Polynomial ℝ) (hg0 : ∀ i ∈ s, (g i).eval 0 = 1) :
    (Polynomial.derivative (∏ i ∈ s, g i)).eval 0 =
      ∑ i ∈ s, (Polynomial.derivative (g i)).eval 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Polynomial.derivative_mul,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
      have hprod : (∏ i ∈ s, g i).eval 0 = 1 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_one fun i hi => hg0 i (Finset.mem_insert_of_mem hi)
      have ha0 : (g a).eval 0 = 1 := hg0 a (Finset.mem_insert_self a s)
      rw [hprod, ha0, ih (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))]
      ring

private theorem sum_Icc_cast_eq (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (j : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring

theorem reciprocalAnnihilator_derivative_eval_zero (k : ℕ) :
    (Polynomial.derivative (reciprocalAnnihilator k)).eval 0 =
      -((k : ℝ) * ((k : ℝ) + 1) / 2) := by
  unfold reciprocalAnnihilator
  rw [eval_derivative_prod_at_zero]
  · have hterm : ∀ j ∈ Finset.Icc 1 k,
        (Polynomial.derivative (1 - Polynomial.C (j : ℝ) * Polynomial.X)).eval 0 = -(j : ℝ) := by
      intro j _
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, sum_Icc_cast_eq]
  · intro j _
    simp

theorem shiftedChebyshevFactor_derivative_eval_zero (k l : ℕ) :
    (Polynomial.derivative (shiftedChebyshevFactor k l)).eval 0 =
      -(2 * (k : ℝ) * (l : ℝ) ^ 2) := by
  unfold shiftedChebyshevFactor
  rw [Polynomial.derivative_comp]
  have hlin : Polynomial.derivative (1 - Polynomial.C (2 * (k : ℝ)) * Polynomial.X) =
      -Polynomial.C (2 * (k : ℝ)) := by
    simp
  rw [Polynomial.eval_mul, hlin]
  have hev : (1 - Polynomial.C (2 * (k : ℝ)) * Polynomial.X).eval 0 = 1 := by simp
  rw [Polynomial.eval_comp, hev, Polynomial.Chebyshev.derivative_T_eval_one]
  simp

theorem reciprocalSharpnessWitness_derivative_eval_zero (k l : ℕ) :
    (Polynomial.derivative (reciprocalSharpnessWitness k l)).eval 0 =
      -((k : ℝ) * ((k : ℝ) + 1) / 2 + 2 * (k : ℝ) * (l : ℝ) ^ 2) := by
  unfold reciprocalSharpnessWitness
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    reciprocalAnnihilator_eval_zero, shiftedChebyshevFactor_eval_zero,
    reciprocalAnnihilator_derivative_eval_zero, shiftedChebyshevFactor_derivative_eval_zero]
  ring

theorem reciprocalSharpnessWitness_derivative_abs_at_zero (k l : ℕ) :
    |(Polynomial.derivative (reciprocalSharpnessWitness k l)).eval 0| =
      (k : ℝ) * ((k : ℝ) + 1) / 2 + 2 * (k : ℝ) * (l : ℝ) ^ 2 := by
  rw [reciprocalSharpnessWitness_derivative_eval_zero, abs_neg, abs_of_nonneg (by positivity)]

/-- For `k = ℓ = m ≥ 1`, `|P_{m,m}'(0)| = 2m^3 + m(m+1)/2 ≥ 2m^3 > m^2`,
witnessing cubic derivative growth on the reciprocal lattice against quadratic Markov scaling. -/
theorem reciprocalSharpnessWitness_cubic_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ 2 < |(Polynomial.derivative (reciprocalSharpnessWitness m m)).eval 0| ∧
      2 * (m : ℝ) ^ 3 ≤ |(Polynomial.derivative (reciprocalSharpnessWitness m m)).eval 0| := by
  rw [reciprocalSharpnessWitness_derivative_abs_at_zero]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcubic : 2 * (m : ℝ) ^ 3 ≤ (m : ℝ) * ((m : ℝ) + 1) / 2 + 2 * (m : ℝ) * (m : ℝ) ^ 2 := by
    have h1 : (m : ℝ) * ((m : ℝ) + 1) / 2 ≥ 0 := by positivity
    nlinarith
  have hsq : (m : ℝ) ^ 2 < 2 * (m : ℝ) ^ 3 := by
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  exact ⟨lt_of_lt_of_le hsq hcubic, hcubic⟩

end RhAstraSynthesis
