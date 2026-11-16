import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import RhAstraSynthesis.CoprimeMobiusFinite
import RhAstraSynthesis.MobiusHarmonicBound

/-!
# Actual coprime Möbius convolution

Defines the coprime-filtered kernel `actualCoprimeKernel d n` as the divisor
transform of `filteredMobiusValue d`, proves the exact Dirichlet-convolution
factorization `actual_coprime_mobius_factorization` via Möbius inversion,
computes explicit prime-power values, establishes multiplicativity and
unit-interval bounds (`0 ≤ g_d(n) ≤ 1`), and bounds the filtered weighted mass
`coprime_weighted_mass_abs_le_kernel_mass`.
-/

namespace RhAstraSynthesis

noncomputable def filteredMobiusValue (d n : ℕ) : ℝ :=
  if n.Coprime d then CoprimeMobius.f n else 0

noncomputable def actualCoprimeKernel (d n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors, filteredMobiusValue d a

/-- The actual filtered coefficient vanishes on nonsquarefree prime powers. -/
theorem filtered_mobius_prime_power (d p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k ≠ 0) :
    filteredMobiusValue d (p ^ k) =
      if k = 1 then (if p ∣ d then 0 else -(p : ℝ) / ((p : ℝ) + 1)) else 0 := by
  have hr : CoprimeMobius.r (p ^ k) = (p : ℝ) / ((p : ℝ) + 1) := by
    simp [CoprimeMobius.r, Nat.primeFactors_prime_pow hk hp]
  by_cases hk1 : k = 1
  · subst k
    have hcop : p.Coprime d ↔ ¬p ∣ d := hp.coprime_iff_not_dvd
    simp only [pow_one] at hr
    by_cases hpd : p ∣ d
    · simp [filteredMobiusValue, hcop, hpd]
    · simp [filteredMobiusValue, hcop, hpd, CoprimeMobius.f,
        ArithmeticFunction.moebius_apply_prime hp, hr]
      ring
  · simp [filteredMobiusValue, CoprimeMobius.f,
      ArithmeticFunction.moebius_apply_prime_pow hp hk, hk1]

/-- The divisor-transform kernel has the prescribed local coprime-filter weights. -/
theorem actual_coprime_kernel_prime_power (d p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k ≠ 0) :
    actualCoprimeKernel d (p ^ k) = if p ∣ d then 1 else 1 / ((p : ℝ) + 1) := by
  have hf1 : filteredMobiusValue d 1 = 1 := by
    simp [filteredMobiusValue, CoprimeMobius.f, CoprimeMobius.r]
  have hfp : filteredMobiusValue d p =
      if p ∣ d then 0 else -(p : ℝ) / ((p : ℝ) + 1) := by
    simpa using filtered_mobius_prime_power d p hp 1 (by decide)
  rw [actualCoprimeKernel, Nat.sum_divisors_prime_pow hp]
  cases k with
  | zero => contradiction
  | succ j =>
      clear hk
      induction j with
      | zero =>
          norm_num only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero,
            zero_add, pow_zero, pow_one]
          rw [hf1, hfp]
          by_cases hpd : p ∣ d
          · simp [hpd]
          · simp only [hpd, ↓reduceIte]
            have hden : (p : ℝ) + 1 ≠ 0 := by positivity
            field_simp [hden]
            ring
      | succ j ih =>
          rw [Finset.sum_range_succ]
          have hz : filteredMobiusValue d (p ^ (j + 1 + 1)) = 0 := by
            rw [filtered_mobius_prime_power d p hp (j + 1 + 1) (by omega)]
            simp
          rw [hz, add_zero]
          exact ih

/-- Möbius inversion with the actual arithmetic weight, written as Dirichlet convolution. -/
theorem actual_coprime_mobius_factorization (d n : ℕ) (hn : 0 < n) :
    (∑ a ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius a.1 : ℝ) * actualCoprimeKernel d a.2) =
      CoprimeMobius.f n * (if n.Coprime d then 1 else 0) := by
  have hsum : ∀ m > 0, ∑ i ∈ m.divisors, filteredMobiusValue d i = actualCoprimeKernel d m := by
    intro m hm
    rfl
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := filteredMobiusValue d) (g := actualCoprimeKernel d)).mp hsum n hn
  simpa [filteredMobiusValue, mul_ite] using h

private noncomputable def harmonicMoebiusAF : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (ArithmeticFunction.moebius n : ℝ) / (n : ℝ), by simp⟩

private noncomputable def harmonicCoprimeKernelAF (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ actualCoprimeKernel d n / (n : ℝ), by simp⟩

/-- Exact exponent-one weighted convolution, for every finite cutoff (including zero). -/
theorem actual_coprime_weighted_mass (d N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, filteredMobiusValue d n / (n : ℝ)) =
      ∑ k ∈ Finset.Ioc 0 N, (actualCoprimeKernel d k / (k : ℝ)) *
        ∑ m ∈ Finset.Ioc 0 (N / k), (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) := by
  have hconv (n : ℕ) : (harmonicCoprimeKernelAF d * harmonicMoebiusAF) n =
      filteredMobiusValue d n / (n : ℝ) := by
    by_cases hn : n = 0
    · subst n
      simp
    · rw [mul_comm, ArithmeticFunction.mul_apply]
      calc
        _ = (∑ a ∈ n.divisorsAntidiagonal,
            (ArithmeticFunction.moebius a.1 : ℝ) * actualCoprimeKernel d a.2) / (n : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a ha
          change ((ArithmeticFunction.moebius a.1 : ℝ) / (a.1 : ℝ)) *
            (actualCoprimeKernel d a.2 / (a.2 : ℝ)) =
            ((ArithmeticFunction.moebius a.1 : ℝ) * actualCoprimeKernel d a.2) / (n : ℝ)
          rw [div_mul_div_comm, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp ha).1]
        _ = filteredMobiusValue d n / (n : ℝ) := by
          rw [actual_coprime_mobius_factorization d n (Nat.pos_of_ne_zero hn)]
          by_cases hc : n.Coprime d <;> simp [filteredMobiusValue, hc]
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (harmonicCoprimeKernelAF d) harmonicMoebiusAF N
  simp_rw [hconv] at h
  simpa only [harmonicCoprimeKernelAF, harmonicMoebiusAF, ArithmeticFunction.coe_mk] using h

private noncomputable def filteredMobiusAF (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨filteredMobiusValue d, by simp [filteredMobiusValue, CoprimeMobius.f]⟩

/-- The actual divisor-transform kernel as an arithmetic function, including its zero value. -/
noncomputable def actualCoprimeKernelAF (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨actualCoprimeKernel d, by simp [actualCoprimeKernel]⟩

private theorem isMultiplicative_filteredMobiusAF (d : ℕ) :
    (filteredMobiusAF d).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [filteredMobiusAF, filteredMobiusValue, CoprimeMobius.f, CoprimeMobius.r]
  · intro a b hab
    change filteredMobiusValue d (a * b) = filteredMobiusValue d a * filteredMobiusValue d b
    have hr : CoprimeMobius.r (a * b) = CoprimeMobius.r a * CoprimeMobius.r b := by
      simp only [CoprimeMobius.r, hab.primeFactors_mul]
      exact Finset.prod_union hab.disjoint_primeFactors
    have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
    have hf : CoprimeMobius.f (a * b) = CoprimeMobius.f a * CoprimeMobius.f b := by
      simp only [CoprimeMobius.f, hr, hmu, Int.cast_mul]
      ring
    simp only [filteredMobiusValue, Nat.coprime_mul_iff_left]
    split_ifs <;> first | exact hf | (exfalso; tauto) | ring

/-- Multiplicativity is derived from the actual filtered weight and zeta convolution. -/
theorem isMultiplicative_actualCoprimeKernelAF (d : ℕ) :
    (actualCoprimeKernelAF d).IsMultiplicative := by
  have heq : actualCoprimeKernelAF d =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * filteredMobiusAF d := by
    ext n
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    rfl
  rw [heq]
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (isMultiplicative_filteredMobiusAF d)

/-- The local weights determine the actual kernel at every nonzero integer. -/
theorem actual_coprime_kernel_eq_prime_product (d n : ℕ) (hn : n ≠ 0) :
    actualCoprimeKernel d n =
      ∏ p ∈ n.primeFactors, (if p ∣ d then 1 else 1 / ((p : ℝ) + 1)) := by
  have h := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (actualCoprimeKernelAF d) (isMultiplicative_actualCoprimeKernelAF d) hn
  change actualCoprimeKernel d n =
    ∏ p ∈ n.primeFactors, actualCoprimeKernel d (p ^ n.factorization p) at h
  rw [h]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hk := hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  exact actual_coprime_kernel_prime_power d p hprime (n.factorization p) (Nat.ne_of_gt hk)

/-- Nonnegativity of `actualCoprimeKernel`. -/
theorem actual_coprime_kernel_nonneg (d n : ℕ) : 0 ≤ actualCoprimeKernel d n := by
  by_cases hn : n = 0
  · subst n
    simp [actualCoprimeKernel]
  · rw [actual_coprime_kernel_eq_prime_product d n hn]
    apply Finset.prod_nonneg
    intro p hp
    split_ifs <;> positivity

/-- Every actual coprime-kernel coefficient lies in the unit interval. -/
theorem actual_coprime_kernel_le_one (d n : ℕ) : actualCoprimeKernel d n ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [actualCoprimeKernel]
  · rw [actual_coprime_kernel_eq_prime_product d n hn]
    calc
      _ ≤ ∏ _p ∈ n.primeFactors, (1 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          split_ifs <;> positivity
        · intro p hp
          split_ifs
          · exact le_rfl
          · apply (div_le_one (by positivity)).mpr
            have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
            linarith
      _ = 1 := by simp

/-- The verified Möbius bound controls the actual finite coprime harmonic mass. -/
theorem coprime_weighted_mass_abs_le_kernel_mass (d N : ℕ) :
    |∑ n ∈ Finset.Ioc 0 N, filteredMobiusValue d n / (n : ℝ)| ≤
      ∑ k ∈ Finset.Ioc 0 N, actualCoprimeKernel d k / (k : ℝ) := by
  rw [actual_coprime_weighted_mass]
  calc
    _ ≤ ∑ k ∈ Finset.Ioc 0 N,
        |(actualCoprimeKernel d k / (k : ℝ)) *
          ∑ m ∈ Finset.Ioc 0 (N / k), (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hK : 0 ≤ actualCoprimeKernel d k / (k : ℝ) :=
        div_nonneg (actual_coprime_kernel_nonneg d k) (Nat.cast_nonneg k)
      have hM : |∑ m ∈ Finset.Ioc 0 (N / k),
          (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)| ≤ 1 := by
        by_cases hq : (N / k : ℕ) = 0
        · simp [hq]
        · exact moebius_harmonic_abs_le_one (N / k) (Nat.pos_of_ne_zero hq)
      rw [abs_mul, abs_of_nonneg hK]
      calc
        _ ≤ (actualCoprimeKernel d k / (k : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hM hK
        _ = _ := mul_one _

end RhAstraSynthesis
