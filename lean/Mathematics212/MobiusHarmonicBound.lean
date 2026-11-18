import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Elementary uniform bound for the actual harmonic Möbius sum

Proves the classical floor identity `moebius_floor_identity` from `μ * ζ = 1`
and deduces via Euclidean division with nonnegative remainders the uniform bound
`moebius_harmonic_abs_le_one`: `|∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) / n| ≤ 1` for all `N ≥ 1`.
-/

namespace Mathematics212

/-- Summing `μ * ζ = 1` gives the exact floor identity for a positive integer cutoff. -/
theorem moebius_floor_identity (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N,
      (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ)) = 1 := by
  have hmem : 1 ∈ Finset.Ioc 0 N := by simp; omega
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) N
  simpa [ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, hmem] using h.symm

private theorem real_division_with_remainder (N n : ℕ) (hn : 0 < n) :
    (N : ℝ) / (n : ℝ) = ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcast : (n : ℝ) * ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N n
  field_simp [hnR]
  nlinarith

/-- Classical bound `|∑_{1 ≤ n ≤ N} μ(n)/n| ≤ 1` for the actual Mathlib Möbius function. -/
theorem moebius_harmonic_abs_le_one (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 := by
  have hmem : 1 ∈ Finset.Ioc 0 N := by simp; omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hdecomp : (N : ℝ) *
      (∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =
      1 + ∑ n ∈ Finset.Ioc 0 N,
        (ArithmeticFunction.moebius n : ℝ) * (((N % n : ℕ) : ℝ) / (n : ℝ)) := by
    calc
      _ = ∑ n ∈ Finset.Ioc 0 N,
          (ArithmeticFunction.moebius n : ℝ) * ((N : ℝ) / (n : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = ∑ n ∈ Finset.Ioc 0 N,
          (ArithmeticFunction.moebius n : ℝ) *
            (((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) / (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [real_division_with_remainder N n (Finset.mem_Ioc.mp hn).1]
      _ = (∑ n ∈ Finset.Ioc 0 N,
          (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ)) +
          ∑ n ∈ Finset.Ioc 0 N,
            (ArithmeticFunction.moebius n : ℝ) * (((N % n : ℕ) : ℝ) / (n : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by rw [moebius_floor_identity N hN]
  have hterm (n : ℕ) (hn : n ∈ Finset.Ioc 0 N) :
      |(ArithmeticFunction.moebius n : ℝ) * (((N % n : ℕ) : ℝ) / (n : ℝ))| ≤
        if n = 1 then 0 else 1 := by
    by_cases hone : n = 1
    · subst n
      simp [Nat.mod_one]
    · have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hr0 : (0 : ℝ) ≤ ((N % n : ℕ) : ℝ) / (n : ℝ) := by positivity
      have hr1 : ((N % n : ℕ) : ℝ) / (n : ℝ) ≤ 1 :=
        (div_le_one hnR).2 (le_of_lt (by exact_mod_cast Nat.mod_lt N hnpos))
      have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      simp only [hone, ↓reduceIte, abs_mul, abs_of_nonneg hr0]
      calc
        _ ≤ 1 * (((N % n : ℕ) : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hmu hr0
        _ ≤ 1 := by simpa using hr1
  have hcount : (∑ n ∈ Finset.Ioc 0 N, if n = 1 then (0 : ℝ) else 1) = (N : ℝ) - 1 := by
    have hpoint (n : ℕ) : (if n = 1 then (0 : ℝ) else 1) =
        1 - (if n = 1 then (1 : ℝ) else 0) := by
      by_cases hn : n = 1 <;> simp [hn]
    simp_rw [hpoint, Finset.sum_sub_distrib]
    simp [hmem]
  have hsum : (∑ n ∈ Finset.Ioc 0 N,
      |(ArithmeticFunction.moebius n : ℝ) * (((N % n : ℕ) : ℝ) / (n : ℝ))|) ≤
      (N : ℝ) - 1 := by
    exact (Finset.sum_le_sum hterm).trans_eq hcount
  have hbound : |(N : ℝ) *
      (∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))| ≤ (N : ℝ) := by
    rw [hdecomp]
    calc
      _ ≤ 1 + |∑ n ∈ Finset.Ioc 0 N,
          (ArithmeticFunction.moebius n : ℝ) * (((N % n : ℕ) : ℝ) / (n : ℝ))| := by
        simpa using abs_add_le (1 : ℝ) (∑ n ∈ Finset.Ioc 0 N,
          (ArithmeticFunction.moebius n : ℝ) * (((N % n : ℕ) : ℝ) / (n : ℝ)))
      _ ≤ 1 + ∑ n ∈ Finset.Ioc 0 N,
          |(ArithmeticFunction.moebius n : ℝ) * (((N % n : ℕ) : ℝ) / (n : ℝ))| :=
        by
          have habs := Finset.abs_sum_le_sum_abs
            (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℝ) *
              (((N % n : ℕ) : ℝ) / (n : ℝ))) (Finset.Ioc 0 N)
          linarith
      _ ≤ 1 + ((N : ℝ) - 1) := by linarith [hsum]
      _ = (N : ℝ) := by ring
  have hscale : (N : ℝ) *
      |∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ (N : ℝ) := by
    simpa [abs_mul, abs_of_pos hNpos] using hbound
  by_contra hfail
  have hgt : 0 <
      |∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| - 1 :=
    sub_pos.mpr (lt_of_not_ge hfail)
  have hpos := mul_pos hNpos hgt
  nlinarith

end Mathematics212
