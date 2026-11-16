import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open ArithmeticFunction
open scoped BigOperators

namespace CoprimeMobiusSigned

/-!
Exact finite Möbius-inversion signed-square identity `weightedG_eq_signed_square`,
valid for arbitrary finite weight and inverse factor sequences on squarefree support.
-/

private theorem triple_square (s : Finset ℕ) (c : ℕ → ℝ) (v : ℕ → ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s, c d * v d a * v d b) =
      ∑ d ∈ s, c d * (∑ a ∈ s, v d a)^2 := by
  have hswap :
      (∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s, c d * v d a * v d b) =
        ∑ d ∈ s, ∑ a ∈ s, ∑ b ∈ s, c d * v d a * v d b := by
    calc
      _ = ∑ a ∈ s, ∑ d ∈ s, ∑ b ∈ s, c d * v d a * v d b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    (∑ a ∈ s, ∑ b ∈ s, c d * v d a * v d b) =
        (∑ a ∈ s, c d * v d a) * (∑ b ∈ s, v d b) := by
          rw [Finset.sum_mul_sum]
    _ = c d * (∑ a ∈ s, v d a)^2 := by
          rw [← Finset.mul_sum]
          ring

private theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] using h

private theorem coprime_mask (a b N : ℕ) (ha : 0 < a) (haN : a ≤ N) :
    (∑ d ∈ Finset.Icc 1 N,
      if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : ℝ) else 0) =
      if a.Coprime b then 1 else 0 := by
  let g := Nat.gcd a b
  have hg : g ≠ 0 := by
    dsimp [g]
    exact (Nat.gcd_pos_of_pos_left b ha).ne'
  have hsub : g.divisors ⊆ Finset.Icc 1 N := by
    intro d hd
    have hdg : d ∣ g := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdg (Nat.pos_of_ne_zero hg)
    have hdle : d ≤ g := Nat.le_of_dvd (Nat.pos_of_ne_zero hg) hdg
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle.trans ((Nat.gcd_le_left b ha).trans haN)⟩
  calc
    (∑ d ∈ Finset.Icc 1 N,
      if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : ℝ) else 0) =
      ∑ d ∈ Finset.Icc 1 N,
        if d ∈ g.divisors then (ArithmeticFunction.moebius d : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdvd : d ∣ g ↔ d ∣ a ∧ d ∣ b := Nat.dvd_gcd_iff
          simp [Nat.mem_divisors, hg, hdvd]
    _ = ∑ d ∈ g.divisors,
        if d ∈ g.divisors then (ArithmeticFunction.moebius d : ℝ) else 0 := by
          exact (Finset.sum_subset hsub (by
            intro d hd hnot
            simp [hnot])).symm
    _ = ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          simp [hd]
    _ = if a.Coprime b then 1 else 0 := by
          rw [sum_moebius_divisors]

noncomputable def weightedG (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
    if a.Coprime b then w a * w b else 0

noncomputable def multiples (N d : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, if d ∣ a then w a else 0

theorem weightedG_eq_signed_square (N : ℕ) (w : ℕ → ℝ) :
    weightedG N w =
      ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * (multiples N d w)^2 := by
  let s := Finset.Icc 1 N
  unfold weightedG multiples
  change (∑ a ∈ s, ∑ b ∈ s, if a.Coprime b then w a * w b else 0) =
    ∑ d ∈ s, (ArithmeticFunction.moebius d : ℝ) *
      (∑ a ∈ s, if d ∣ a then w a else 0)^2
  calc
    (∑ a ∈ s, ∑ b ∈ s, if a.Coprime b then w a * w b else 0) =
        ∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s,
          (ArithmeticFunction.moebius d : ℝ) *
            (if d ∣ a then w a else 0) * (if d ∣ b then w b else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
      have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
      calc
        (if a.Coprime b then w a * w b else 0) =
            (if a.Coprime b then (1 : ℝ) else 0) * w a * w b := by
              split_ifs <;> ring
        _ = (∑ d ∈ s,
              if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : ℝ) else 0) *
              w a * w b := by
                rw [coprime_mask a b N haPos haN]
        _ = ∑ d ∈ s, (ArithmeticFunction.moebius d : ℝ) *
              (if d ∣ a then w a else 0) * (if d ∣ b then w b else 0) := by
                rw [Finset.sum_mul, Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hda : d ∣ a <;> by_cases hdb : d ∣ b <;>
                  simp [hda, hdb]
    _ = ∑ d ∈ s, (ArithmeticFunction.moebius d : ℝ) *
          (∑ a ∈ s, if d ∣ a then w a else 0)^2 := by
          exact triple_square s (fun d => (ArithmeticFunction.moebius d : ℝ))
            (fun d a => if d ∣ a then w a else 0)

end CoprimeMobiusSigned
