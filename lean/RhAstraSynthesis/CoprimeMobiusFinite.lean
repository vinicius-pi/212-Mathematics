import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Finite coprime Möbius quadratic sum identities

Formalizes the finite arithmetic factorization equating the coprime quadratic sum
`Goriginal N` with `G N` and the uncoupled product sum `Gproduct N` using the
multiplicativity of `μ(n) / ψ(n)`.
-/

namespace CoprimeMobius

open ArithmeticFunction

noncomputable def psi (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, ((p : ℝ) + 1)

noncomputable def muWeight (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) / psi n

noncomputable def r (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) + 1))

noncomputable def f (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * r n

noncomputable def G (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
    if a.Coprime b then muWeight a * muWeight b else 0

noncomputable def Gproduct (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, muWeight (a * b)

noncomputable def Goriginal (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
    if a.Coprime b then (f a / (a : ℝ)) * (f b / (b : ℝ)) else 0

theorem psi_pos (n : ℕ) : 0 < psi n := by
  unfold psi
  apply Finset.prod_pos
  intro p hp
  positivity

theorem r_eq_div_psi_of_squarefree {n : ℕ} (hn : Squarefree n) :
    r n = (n : ℝ) / psi n := by
  unfold r psi
  rw [Finset.prod_div_distrib]
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]

theorem f_div_eq_muWeight {n : ℕ} (hn : 0 < n) :
    f n / (n : ℝ) = muWeight n := by
  by_cases hs : Squarefree n
  · rw [f, r_eq_div_psi_of_squarefree hs]
    unfold muWeight
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hp0 : psi n ≠ 0 := ne_of_gt (psi_pos n)
    field_simp
  · simp [f, muWeight, moebius_eq_zero_of_not_squarefree hs]

theorem psi_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) :
    psi (a * b) = psi a * psi b := by
  simp only [psi, hab.primeFactors_mul]
  exact Finset.prod_union hab.disjoint_primeFactors

theorem muWeight_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) :
    muWeight (a * b) = muWeight a * muWeight b := by
  simp only [muWeight, psi_mul_of_coprime hab]
  rw [IsMultiplicative.map_mul_of_coprime isMultiplicative_moebius hab]
  push_cast
  ring

theorem muWeight_mul_of_not_coprime {a b : ℕ} (hab : ¬a.Coprime b) :
    muWeight (a * b) = 0 := by
  have hs : ¬Squarefree (a * b) := by
    intro hs
    exact hab (Nat.coprime_of_squarefree_mul hs)
  simp [muWeight, moebius_eq_zero_of_not_squarefree hs]

theorem G_eq_Gproduct (N : ℕ) : G N = Gproduct N := by
  unfold G Gproduct
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : a.Coprime b
  · simp [hab, muWeight_mul_of_coprime hab]
  · simp [hab, muWeight_mul_of_not_coprime hab]

theorem Goriginal_eq_G (N : ℕ) : Goriginal N = G N := by
  unfold Goriginal G
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ha0 : 0 < a := lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Icc.mp ha).1
  have hb0 : 0 < b := lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Icc.mp hb).1
  rw [f_div_eq_muWeight ha0, f_div_eq_muWeight hb0]

theorem Goriginal_eq_Gproduct (N : ℕ) : Goriginal N = Gproduct N :=
  (Goriginal_eq_G N).trans (G_eq_Gproduct N)

end CoprimeMobius
