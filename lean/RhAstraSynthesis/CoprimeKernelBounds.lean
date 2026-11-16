import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic
import RhAstraSynthesis.ActualCoprimeConvolution

/-!
# Pointwise majorants for the actual coprime kernel

Establishes exact divisor-ratio evaluations `actual_coprime_kernel_eq_psi_gcd_div`
and `actual_coprime_kernel_base_eq_inv_psi`, the modulus-uniform majorant
`actual_coprime_kernel_le_psi_mul_base`, and the squarefree/square decomposition
`exists_squarefree_kernel_majorant` preparing the convergent `s > 1/2` moment series.
-/

namespace RhAstraSynthesis

/-- The prime-factor product `psi` is monotone under divisibility into a nonzero integer. -/
theorem coprime_psi_le_of_dvd {a n : ℕ} (han : a ∣ n) (hn : n ≠ 0) :
    CoprimeMobius.psi a ≤ CoprimeMobius.psi n := by
  have hNat : (∏ p ∈ a.primeFactors, (p + 1)) ≤ ∏ p ∈ n.primeFactors, (p + 1) := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Nat.primeFactors_mono han hn)
    intro p hp hpa
    omega
  unfold CoprimeMobius.psi
  exact_mod_cast hNat

/-- A squarefree divisor pays for its primes inside the actual denominator product. -/
theorem squarefree_divisor_le_coprime_psi {a n : ℕ} (ha : Squarefree a)
    (han : a ∣ n) (hn : n ≠ 0) : (a : ℝ) ≤ CoprimeMobius.psi n := by
  calc
    (a : ℝ) = ∏ p ∈ a.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ha]
    _ ≤ ∏ p ∈ a.primeFactors, ((p : ℝ) + 1) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact Nat.cast_nonneg p
      · intro p hp
        linarith
    _ = CoprimeMobius.psi a := rfl
    _ ≤ CoprimeMobius.psi n := coprime_psi_le_of_dvd han hn

/-- Exact gcd-ratio formula for the actual kernel, including modulus zero. -/
theorem actual_coprime_kernel_eq_psi_gcd_div (d n : ℕ) (hn : n ≠ 0) :
    actualCoprimeKernel d n = CoprimeMobius.psi (n.gcd d) / CoprimeMobius.psi n := by
  have hset : n.primeFactors.filter (fun p ↦ p ∣ d) = (n.gcd d).primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpn, hn'⟩, hpd⟩
      exact ⟨hp, Nat.dvd_gcd hpn hpd, Nat.gcd_ne_zero_left hn⟩
    · rintro ⟨hp, hpg, hg⟩
      exact ⟨⟨hp, dvd_trans hpg (Nat.gcd_dvd_left n d), hn⟩,
        dvd_trans hpg (Nat.gcd_dvd_right n d)⟩
  apply (eq_div_iff (ne_of_gt (CoprimeMobius.psi_pos n))).mpr
  rw [actual_coprime_kernel_eq_prime_product d n hn]
  simp only [CoprimeMobius.psi]
  rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ p ∈ n.primeFactors, (if p ∣ d then (p : ℝ) + 1 else 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hpd : p ∣ d
      · simp [hpd]
      · simp [hpd, ne_of_gt (show (0 : ℝ) < (p : ℝ) + 1 by positivity)]
    _ = ∏ p ∈ n.primeFactors.filter (fun p ↦ p ∣ d), ((p : ℝ) + 1) := by
      rw [Finset.prod_filter]
    _ = _ := by rw [hset]

/-- The base kernel is the inverse of the concrete `psi` product at nonzero integers. -/
theorem actual_coprime_kernel_base_eq_inv_psi (n : ℕ) (hn : n ≠ 0) :
    actualCoprimeKernel 1 n = 1 / CoprimeMobius.psi n := by
  simpa [CoprimeMobius.psi] using actual_coprime_kernel_eq_psi_gcd_div 1 n hn

/-- A coarse fixed-modulus domination used for convergence, not the sharp `tau(d)` bound. -/
theorem actual_coprime_kernel_le_psi_mul_base (d n : ℕ) (hd : d ≠ 0) :
    actualCoprimeKernel d n ≤ CoprimeMobius.psi d * actualCoprimeKernel 1 n := by
  by_cases hn : n = 0
  · subst n
    simp [actualCoprimeKernel]
  · rw [actual_coprime_kernel_eq_psi_gcd_div d n hn,
      actual_coprime_kernel_base_eq_inv_psi n hn]
    have hpsi := coprime_psi_le_of_dvd (Nat.gcd_dvd_right n d) hd
    have h := mul_le_mul_of_nonneg_right hpsi
      (inv_nonneg.mpr (CoprimeMobius.psi_pos n).le)
    simpa only [div_eq_mul_inv, one_mul] using h

/-- Squarefree/square decomposition with the actual base-kernel majorant attached. -/
theorem exists_squarefree_kernel_majorant (n : ℕ) (hn : 0 < n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a ∧
      actualCoprimeKernel 1 n ≤ 1 / (a : ℝ) := by
  obtain ⟨a, b, ha, hb, heq, hs⟩ := Nat.sq_mul_squarefree_of_pos hn
  have han : a ∣ n := ⟨b ^ 2, heq.symm.trans (Nat.mul_comm _ _)⟩
  refine ⟨a, b, ha, hb, heq, hs, ?_⟩
  rw [actual_coprime_kernel_base_eq_inv_psi n (Nat.ne_of_gt hn)]
  exact one_div_le_one_div_of_le (by exact_mod_cast ha)
    (squarefree_divisor_le_coprime_psi hs han (Nat.ne_of_gt hn))

end RhAstraSynthesis
