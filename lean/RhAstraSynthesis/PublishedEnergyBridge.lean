import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Truncated Baez-Duarte Energy Identity

Defines the truncated Möbius divisor sum `truncatedInverse u n` and its
complement `tailDivisorSum u n` over `ArithmeticFunction.moebius`, and proves
the exact finite L² energy shift `finite_energy_exact`.
-/

namespace PublishedEnergyBridge

open scoped BigOperators
open ArithmeticFunction

def truncatedInverse (u n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (· ≤ u), ArithmeticFunction.moebius d

def tailDivisorSum (u n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => u < d), ArithmeticFunction.moebius d

/-- The tail divisor sum complements the truncated Möbius prefix sum against `δ(n)`. -/
theorem tail_prefix_complement (u n : ℕ) :
    tailDivisorSum u n = (if n = 1 then (1 : ℤ) else 0) - truncatedInverse u n := by
  have hfilter : n.divisors.filter (fun d => u < d) =
      n.divisors.filter (fun d => ¬ d ≤ u) := by
    ext d
    simp [not_le]
  have hsum : truncatedInverse u n + tailDivisorSum u n =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d := by
    unfold truncatedInverse tailDivisorSum
    rw [hfilter]
    exact Finset.sum_filter_add_sum_filter_not n.divisors (· ≤ u)
      (fun d => ArithmeticFunction.moebius d)
  have hinv : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then (1 : ℤ) else 0 := by
    have hZ := congrArg (fun F : ArithmeticFunction ℤ => F n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℤ))
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
      ArithmeticFunction.intCoe_apply, Int.cast_id] using hZ
  omega

theorem square_terms (u n : ℕ) (hu : 1 ≤ u) :
    tailDivisorSum u n ^ 2 =
      truncatedInverse u n ^ 2 - (if n = 1 then (1 : ℤ) else 0) := by
  by_cases hn : n = 1
  · subst n
    have hp : truncatedInverse u 1 = 1 := by
      unfold truncatedInverse
      rw [Nat.divisors_one, Finset.filter_singleton, ite_eq_left_iff.mpr (fun h => absurd hu h),
        Finset.sum_singleton]
      simp
    have ht : tailDivisorSum u 1 = 0 := by
      rw [tail_prefix_complement, hp]
      simp
    simp [hp, ht]
  · have ht : tailDivisorSum u n = -truncatedInverse u n := by
      rw [tail_prefix_complement]
      simp [hn]
    rw [ht, neg_sq]
    simp [hn]

theorem finite_energy_exact (u Y : ℕ) (hu : 1 ≤ u) (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 Y, tailDivisorSum u n ^ 2) =
      (∑ n ∈ Finset.Icc 1 Y, truncatedInverse u n ^ 2) - 1 := by
  have hcongr : (∑ n ∈ Finset.Icc 1 Y, tailDivisorSum u n ^ 2) =
      ∑ n ∈ Finset.Icc 1 Y,
        (truncatedInverse u n ^ 2 - (if n = 1 then (1 : ℤ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n _
    exact square_terms u n hu
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨le_rfl, hY⟩
  rw [hcongr, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp [h1]

#print axioms tail_prefix_complement
#print axioms square_terms
#print axioms finite_energy_exact

end PublishedEnergyBridge
