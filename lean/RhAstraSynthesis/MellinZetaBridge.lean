import RhAstraSynthesis.CoprimeMobiusSigned
import RhAstraSynthesis.CoprimeMobiusFinite
import RhAstraSynthesis.PrimePowerMellin

/-!
# Coprime Signed-Square Algebra & Mellin–Zeta Bridges

Clean compositional interfaces free of `Lean.Grind.CommRing` typeclass collisions:
1. `coprime_product_eq_signed_square`: equates `CoprimeMobius.Gproduct N` with
   `CoprimeMobiusSigned.weightedG`.
2. `coprime_signed_square_commRing`: generic `_root_.CommRing R` formulation of
   the coprime quadratic signed-square identity.
-/

namespace RhAstraSynthesis

open scoped BigOperators
open ArithmeticFunction

/-- Connects `CoprimeMobius.Gproduct N` from `CoprimeMobiusFinite` to the
signed Möbius square sum in `CoprimeMobiusSigned`. -/
theorem coprime_product_eq_signed_square (N : ℕ) :
    CoprimeMobius.Gproduct N =
      ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) *
          (CoprimeMobiusSigned.multiples N d (fun n => CoprimeMobius.f n / (n : ℝ))) ^ 2 := by
  have h1 : CoprimeMobius.Gproduct N = CoprimeMobius.Goriginal N :=
    (CoprimeMobius.Goriginal_eq_Gproduct N).symm
  have h2 : CoprimeMobius.Goriginal N =
      CoprimeMobiusSigned.weightedG N (fun n => CoprimeMobius.f n / (n : ℝ)) := by
    rfl
  rw [h1, h2, CoprimeMobiusSigned.weightedG_eq_signed_square]

/-- Generic commutative-ring signed-square identity for coprime quadratic forms,
explicitly parameterized over `_root_.CommRing R` to avoid `Lean.Grind.CommRing` collisions. -/
theorem coprime_signed_square_commRing {R : Type*} [_root_.CommRing R]
    (w : ℕ → R) (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a.Coprime b then w a * w b else 0) =
      ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : R) *
          (∑ a ∈ Finset.Icc 1 N, if d ∣ a then w a else 0) ^ 2 := by
  let s := Finset.Icc 1 N
  have hcop : ∀ a ∈ s, ∀ b ∈ s,
      (if a.Coprime b then (1 : R) else 0) =
        ∑ d ∈ s, if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : R) else 0 := by
    intro a ha b hb
    have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
    let g := Nat.gcd a b
    have hg : 0 < g := Nat.gcd_pos_of_pos_left b haPos
    have hga : g ≤ a := Nat.gcd_le_left b haPos
    have hsub : g.divisors ⊆ s := by
      intro d hd
      have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hdle : d ≤ N := (Nat.le_of_dvd hg hdg).trans (hga.trans haN)
      exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
    have hfilter :
        (∑ d ∈ s, if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : R) else 0) =
          ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : R) := by
      calc
        (∑ d ∈ s, if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : R) else 0)
            = ∑ d ∈ s, if d ∈ g.divisors then (ArithmeticFunction.moebius d : R) else 0 := by
              apply Finset.sum_congr rfl
              intro d _
              have hdvd : d ∣ g ↔ d ∣ a ∧ d ∣ b := Nat.dvd_gcd_iff
              simp [Nat.mem_divisors, hg.ne', hdvd]
        _ = ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : R) := by
              rw [← Finset.sum_filter]
              apply Finset.sum_congr
              · ext d
                simp only [Finset.mem_filter, and_iff_right_iff_imp]
                exact fun hd => hsub hd
              · intro _ _; rfl
    rw [hfilter]
    have hZ := congrArg (fun F : ArithmeticFunction R => F g)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := R))
    have hZ' : (∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : R)) =
        if g = 1 then (1 : R) else 0 := by
      simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
        ArithmeticFunction.intCoe_apply] using hZ
    rw [hZ']
  calc
    (∑ a ∈ s, ∑ b ∈ s, if a.Coprime b then w a * w b else 0)
        = ∑ a ∈ s, ∑ b ∈ s,
            (∑ d ∈ s, if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : R) else 0) *
              w a * w b := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [← hcop a ha b hb]
          split_ifs <;> ring
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s,
          (ArithmeticFunction.moebius d : R) *
            (if d ∣ a then w a else 0) * (if d ∣ b then w b else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d _
          by_cases hda : d ∣ a <;> by_cases hdb : d ∣ b <;> simp [hda, hdb]
    _ = ∑ a ∈ s, ∑ d ∈ s, ∑ b ∈ s,
          (ArithmeticFunction.moebius d : R) *
            (if d ∣ a then w a else 0) * (if d ∣ b then w b else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
    _ = ∑ d ∈ s, ∑ a ∈ s, ∑ b ∈ s,
          (ArithmeticFunction.moebius d : R) *
            (if d ∣ a then w a else 0) * (if d ∣ b then w b else 0) := Finset.sum_comm
    _ = ∑ d ∈ s, (ArithmeticFunction.moebius d : R) *
          (∑ a ∈ s, if d ∣ a then w a else 0) ^ 2 := by
          apply Finset.sum_congr rfl
          intro d _
          calc
            (∑ a ∈ s, ∑ b ∈ s,
                (ArithmeticFunction.moebius d : R) *
                  (if d ∣ a then w a else 0) * (if d ∣ b then w b else 0))
                = (∑ a ∈ s, (ArithmeticFunction.moebius d : R) *
                      (if d ∣ a then w a else 0)) *
                    (∑ b ∈ s, if d ∣ b then w b else 0) := by
                  rw [Finset.sum_mul_sum]
            _ = (ArithmeticFunction.moebius d : R) *
                  (∑ a ∈ s, if d ∣ a then w a else 0) ^ 2 := by
                  rw [← Finset.mul_sum]
                  ring

#print axioms coprime_product_eq_signed_square
#print axioms coprime_signed_square_commRing

end RhAstraSynthesis
