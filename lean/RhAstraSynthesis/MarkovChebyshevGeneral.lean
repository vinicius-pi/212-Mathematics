import RhAstraSynthesis.MarkovChebyshevEndpoint
import RhAstraSynthesis.MarkovFactorialNormalization
import RhAstraSynthesis.MarkovAffineTransport
import RhAstraSynthesis.ChebyshevExponentialEnvelope
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Endpoint and Exterior Chebyshev–Markov Inequalities and Reciprocal Transport

Generalizes the pinned-Mathlib Chebyshev extremal theorem from normalized
polynomials on `[-1, 1]` to:
1. Arbitrary supremum bounds `B ≥ 0` on `[-1, 1]`;
2. Both endpoints `±1` and the full exterior `|x| ≥ 1`;
3. Closed-form `(∏_{j < s} (m^2 - j^2)) / (2s - 1)!!` endpoint derivative bounds;
4. Unconditional `(2*s)!`-normalized Taylor-coefficient bounds at `t = 0` for any
   polynomial bounded on `[0, 1 / (L * m)]`.
-/

namespace RhAstraSynthesis

open Polynomial

private lemma degree_comp_linear_le (P : Polynomial ℝ) (m : ℕ) (a b : ℝ)
    (hdeg : P.degree ≤ m) :
    (P.comp (C a * Polynomial.X + C b)).degree ≤ m := by
  have hPn : P.natDegree ≤ m := Polynomial.natDegree_le_of_degree_le hdeg
  have hqn : (C a * Polynomial.X + C b).natDegree ≤ 1 := by
    calc
      (C a * Polynomial.X + C b).natDegree
          ≤ max (C a * Polynomial.X).natDegree (C b).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ max ((C a).natDegree + (Polynomial.X : ℝ[X]).natDegree) 0 := by
        gcongr
        · exact Polynomial.natDegree_mul_le
        · simp
      _ ≤ 1 := by simp
  calc
    (P.comp (C a * Polynomial.X + C b)).degree
        ≤ ((P.comp (C a * Polynomial.X + C b)).natDegree : WithBot ℕ) :=
      Polynomial.degree_le_natDegree
    _ ≤ ((P.natDegree * (C a * Polynomial.X + C b).natDegree : ℕ) : WithBot ℕ) := by
      exact_mod_cast Polynomial.natDegree_comp_le
    _ ≤ (m : WithBot ℕ) := by
      exact_mod_cast (by nlinarith : P.natDegree * (C a * Polynomial.X + C b).natDegree ≤ m)

/-- At `x = 1`, the `s`-th iterated derivative of `T_m` over `ℝ` equals the exact
Markov factorial ratio `(∏_{j < s} (m^2 - j^2)) / markovOddDenom s`. -/
theorem chebyshev_iterate_derivative_eval_one_eq
    (m s : ℕ) :
    ((derivative^[s]) (Chebyshev.T ℝ m)).eval 1 =
      (∏ j ∈ Finset.range s, ((m : ℝ) ^ 2 - (j : ℝ) ^ 2)) / markovOddDenom s := by
  have h := Chebyshev.iterate_derivative_T_eval_one_eq_div (𝔽 := ℝ) (n := (m : ℤ)) s
  rw [h]
  congr 1
  · push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  · unfold markovOddDenom
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

/-- For `B ≥ 0`, any polynomial `P` with `deg P ≤ m` and `|P(t)| ≤ B` on `[-1, 1]`
satisfies `|(P^(s))(x)| ≤ B * (T_m^(s))(x)` on the right ray `x ≥ 1`. -/
theorem markov_chebyshev_scaled_derivative_abs_outside
    (P : Polynomial ℝ) (m s : ℕ) {B x : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B) :
    |((derivative^[s]) P).eval x| ≤
      B * ((derivative^[s]) (Chebyshev.T ℝ m)).eval x := by
  rcases eq_or_lt_of_le hB with rfl | hBpos
  · have hzero : ∀ t ∈ Set.Icc (-1 : ℝ) 1, P.eval t = 0 := fun t ht =>
      abs_nonpos_iff.mp (hbounded t ht)
    have hP0 : P = 0 := by
      by_contra hne
      have hinfinite : {t : ℝ | P.IsRoot t}.Infinite :=
        (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono fun t ht => by
          simpa [Polynomial.IsRoot] using hzero t ht
      exact hne (Polynomial.eq_zero_of_infinite_isRoot P hinfinite)
    subst hP0
    simp
  · have hQdeg : (C B⁻¹ * P).degree ≤ m := by
      calc
        (C B⁻¹ * P).degree ≤ (C B⁻¹).degree + P.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (m : WithBot ℕ) := add_le_add Polynomial.degree_C_le hdeg
        _ = m := zero_add _
    have hQbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(C B⁻¹ * P).eval t| ≤ 1 := by
      intro t ht
      rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
      calc
        B⁻¹ * |P.eval t| ≤ B⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hbounded t ht) (inv_nonneg.mpr hB)
        _ = 1 := inv_mul_cancel₀ hBpos.ne'
    have hQ := markov_chebyshev_derivative_abs_outside (C B⁻¹ * P) m s x hx hQdeg hQbounded
    have hcomm : ∀ k : ℕ, (derivative^[k]) (C B⁻¹ * P) = C B⁻¹ * (derivative^[k]) P := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
            Polynomial.derivative_C_mul]
    rw [hcomm s, Polynomial.eval_mul, Polynomial.eval_C, abs_mul,
      abs_of_pos (inv_pos.mpr hBpos)] at hQ
    have hmul := mul_le_mul_of_nonneg_left hQ hB
    rw [← mul_assoc, mul_inv_cancel₀ hBpos.ne', one_mul] at hmul
    exact hmul

/-- Exterior Chebyshev growth bound for all `|x| ≥ 1`: `|P(x)| ≤ B * T_m(|x|)`. -/
theorem chebyshev_exterior_eval_abs_le
    (P : Polynomial ℝ) (m : ℕ) {B x : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ |x|)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B) :
    |P.eval x| ≤ B * (Chebyshev.T ℝ m).eval |x| := by
  by_cases hxp : 0 ≤ x
  · rw [abs_of_nonneg hxp] at hx ⊢
    simpa using markov_chebyshev_scaled_derivative_abs_outside P m 0 hB hx hdeg hbounded
  · have hxn : x ≤ -1 := by
      rw [abs_of_neg (lt_of_not_ge hxp)] at hx
      linarith
    have hxneg : 1 ≤ -x := by linarith
    let R : Polynomial ℝ := P.comp (C (-1 : ℝ) * Polynomial.X + C 0)
    have hRdeg : R.degree ≤ m := degree_comp_linear_le P m (-1) 0 hdeg
    have hRbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |R.eval t| ≤ B := by
      intro t ht
      have hmt : -t ∈ Set.Icc (-1 : ℝ) 1 := by
        rcases Set.mem_Icc.mp ht with ⟨ht1, ht2⟩
        exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
      simpa [R] using hbounded (-t) hmt
    have hR := markov_chebyshev_scaled_derivative_abs_outside R m 0 hB hxneg hRdeg hRbounded
    rw [abs_of_neg (lt_of_not_ge hxp)]
    simpa [R] using hR

/-- Endpoint Markov derivative bound at both `x = 1` and `x = -1`:
`|(P^(s))(±1)| ≤ B * (∏_{j < s} (m^2 - j^2)) / (2s - 1)!!`. -/
theorem markov_endpoint_abs_le
    (P : Polynomial ℝ) (m s : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ B) :
    |((derivative^[s]) P).eval 1| ≤
        B * ((∏ j ∈ Finset.range s, ((m : ℝ) ^ 2 - (j : ℝ) ^ 2)) / markovOddDenom s) ∧
      |((derivative^[s]) P).eval (-1)| ≤
        B * ((∏ j ∈ Finset.range s, ((m : ℝ) ^ 2 - (j : ℝ) ^ 2)) / markovOddDenom s) := by
  have h1 :
      |((derivative^[s]) P).eval 1| ≤
        B * ((∏ j ∈ Finset.range s, ((m : ℝ) ^ 2 - (j : ℝ) ^ 2)) / markovOddDenom s) := by
    rw [← chebyshev_iterate_derivative_eval_one_eq]
    exact markov_chebyshev_scaled_derivative_abs_outside P m s hB le_rfl hdeg hbounded
  let R : Polynomial ℝ := P.comp (C (-1 : ℝ) * Polynomial.X + C 0)
  have hRdeg : R.degree ≤ m := degree_comp_linear_le P m (-1) 0 hdeg
  have hRbounded : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |R.eval t| ≤ B := by
    intro t ht
    have hmt : -t ∈ Set.Icc (-1 : ℝ) 1 := by
      rcases Set.mem_Icc.mp ht with ⟨ht1, ht2⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    simpa [R] using hbounded (-t) hmt
  have hR1 := markov_chebyshev_scaled_derivative_abs_outside R m s hB le_rfl hRdeg hRbounded
  have hEval : ((derivative^[s]) R).eval 1 = (-1 : ℝ) ^ s * ((derivative^[s]) P).eval (-1) := by
    simpa [R] using iterate_derivative_affine_eval P (-1) 0 1 s
  rw [hEval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    chebyshev_iterate_derivative_eval_one_eq] at hR1
  exact ⟨h1, hR1⟩

/-- Unconditional Taylor-coefficient Markov bound at `t = 0` for any polynomial
of degree `≤ m` bounded by `M ≥ 0` on `[0, 1 / (L * m)]` (`L > 0`, `m ≥ 1`, `s ≤ m`):
`|(P^(s))(0)| / s! ≤ M * ((4 * L)^s * m^(3 * s) / (2 * s)!)`. -/
theorem markov_reciprocal_endpoint_factorial_bound
    (P : Polynomial ℝ) (m s : ℕ) {L M : ℝ}
    (hm : 0 < m) (hs : s ≤ m) (hL : 0 < L) (hM : 0 ≤ M)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (0 : ℝ) (1 / (L * (m : ℝ))), |P.eval t| ≤ M) :
    |((derivative^[s]) P).eval 0| / (s.factorial : ℝ) ≤
      M * (((4 * L) ^ s * (m : ℝ) ^ (3 * s)) / ((2 * s).factorial : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  let a : ℝ := 1 / (2 * L * (m : ℝ))
  have ha_pos : 0 < a := by positivity
  let Q : Polynomial ℝ := P.comp (C a * Polynomial.X + C a)
  have hQdeg : Q.degree ≤ m := degree_comp_linear_le P m a a hdeg
  have hQbounded : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |Q.eval y| ≤ M := by
    intro y hy
    rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
    have hmem : a * y + a ∈ Set.Icc (0 : ℝ) (1 / (L * (m : ℝ))) := by
      refine Set.mem_Icc.mpr ⟨?_, ?_⟩
      · have : 0 ≤ y + 1 := by linarith
        nlinarith [mul_nonneg ha_pos.le this]
      · have hle : a * y + a ≤ a * 2 := by nlinarith [ha_pos]
        have h2a : a * 2 = 1 / (L * (m : ℝ)) := by
          dsimp [a]
          field_simp [hL.ne', hmpos.ne']
        linarith
    simpa [Q, Polynomial.eval_comp] using hbounded (a * y + a) hmem
  have hQ_neg1 := (markov_endpoint_abs_le Q m s hM hQdeg hQbounded).2
  have hEval : ((derivative^[s]) Q).eval (-1) = a ^ s * ((derivative^[s]) P).eval 0 := by
    have h := iterate_derivative_affine_eval P a a (-1) s
    simpa [Q, show a * (-1 : ℝ) + a = 0 by ring] using h
  rw [hEval, abs_mul, abs_of_nonneg (pow_nonneg ha_pos.le s)] at hQ_neg1
  have h_inv_a : a⁻¹ = 2 * L * (m : ℝ) := by
    dsimp [a]
    field_simp [hL.ne', hmpos.ne']
  have hPs :
      |((derivative^[s]) P).eval 0| ≤
        M * ((2 * L * (m : ℝ)) ^ s *
          ((∏ j ∈ Finset.range s, ((m : ℝ) ^ 2 - (j : ℝ) ^ 2)) / markovOddDenom s)) := by
    have ha_pow_pos : 0 < a ^ s := pow_pos ha_pos s
    have hdiv := (le_div_iff₀' ha_pow_pos).mpr hQ_neg1
    rw [div_eq_mul_inv, ← inv_pow, h_inv_a] at hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hsfact_pos : (0 : ℝ) < (s.factorial : ℝ) := by positivity
  have hdeg_pow := markov_normalized_product_le_degree_power m s hs
  have hodd_eq : markovOddDenom s = ((2 * s - 1).doubleFactorial : ℝ) := by
    have h1 := markov_odd_factorial_identity s
    have h2 : ((2 * s).factorial : ℝ) =
        ((2 * s - 1).doubleFactorial : ℝ) * ((2 : ℝ) ^ s * (s.factorial : ℝ)) := by
      exact_mod_cast markov_factorial_double_factorial s
    have hp : (0 : ℝ) < (2 : ℝ) ^ s * (s.factorial : ℝ) := by positivity
    nlinarith [h1, h2]
  have h_upper :
      |((derivative^[s]) P).eval 0| / (s.factorial : ℝ) ≤
        M * (((2 * L * (m : ℝ)) ^ s * (m : ℝ) ^ (2 * s)) /
          (((2 * s - 1).doubleFactorial : ℝ) * (s.factorial : ℝ))) := by
    calc
      |((derivative^[s]) P).eval 0| / (s.factorial : ℝ)
          ≤ (M * ((2 * L * (m : ℝ)) ^ s *
              ((∏ j ∈ Finset.range s, ((m : ℝ) ^ 2 - (j : ℝ) ^ 2)) / markovOddDenom s))) /
            (s.factorial : ℝ) := div_le_div_of_nonneg_right hPs hsfact_pos.le
      _ ≤ (M * ((2 * L * (m : ℝ)) ^ s * ((m : ℝ) ^ (2 * s) / markovOddDenom s))) /
            (s.factorial : ℝ) := by
          gcongr
      _ = M * (((2 * L * (m : ℝ)) ^ s * (m : ℝ) ^ (2 * s)) /
            (((2 * s - 1).doubleFactorial : ℝ) * (s.factorial : ℝ))) := by
          rw [hodd_eq]
          ring
  exact markov_factored_bound_transfer _ M L (m : ℝ) s h_upper

/-- Uniform Taylor-coefficient bound on the reciprocal interval. At each point,
translate or reflect a half-length segment to start at zero and apply the endpoint
bound with parameter `2 * L`. This loses `2^s`, but retains `(2*s)!`; it does not
assert the sharp higher-order interior Markov inequality. -/
theorem markov_reciprocal_interval_factorial_bound
    (P : Polynomial ℝ) (m s : ℕ) {L M x : ℝ}
    (hm : 0 < m) (hs : s ≤ m) (hL : 0 < L) (hM : 0 ≤ M)
    (hdeg : P.degree ≤ m)
    (hbounded : ∀ t ∈ Set.Icc (0 : ℝ) (1 / (L * (m : ℝ))), |P.eval t| ≤ M)
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / (L * (m : ℝ)))) :
    |((derivative^[s]) P).eval x| / (s.factorial : ℝ) ≤
      M * (((8 * L) ^ s * (m : ℝ) ^ (3 * s)) / ((2 * s).factorial : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hhalf : 2 * (1 / ((2 * L) * (m : ℝ))) = 1 / (L * (m : ℝ)) := by
    field_simp [hL.ne', hmpos.ne']
  have htransport (a : ℝ) (ha : |a| = 1)
      (himage : ∀ t ∈ Set.Icc (0 : ℝ) (1 / ((2 * L) * (m : ℝ))),
        a * t + x ∈ Set.Icc (0 : ℝ) (1 / (L * (m : ℝ)))) :
      |((derivative^[s]) P).eval x| / (s.factorial : ℝ) ≤
        M * (((8 * L) ^ s * (m : ℝ) ^ (3 * s)) / ((2 * s).factorial : ℝ)) := by
    let Q : Polynomial ℝ := P.comp (C a * Polynomial.X + C x)
    have hQdeg : Q.degree ≤ m := degree_comp_linear_le P m a x hdeg
    have hQbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 / ((2 * L) * (m : ℝ))),
        |Q.eval t| ≤ M := by
      intro t ht
      simpa [Q] using hbounded (a * t + x) (himage t ht)
    have h := markov_reciprocal_endpoint_factorial_bound Q m s hm hs
      (by positivity : 0 < 2 * L) hM hQdeg hQbound
    have heval : |((derivative^[s]) Q).eval 0| =
        |((derivative^[s]) P).eval x| := by
      rw [show ((derivative^[s]) Q).eval 0 =
        a ^ s * ((derivative^[s]) P).eval x by
          simpa [Q] using iterate_derivative_affine_eval P a x 0 s]
      rw [abs_mul, abs_pow, ha, one_pow, one_mul]
    rw [heval] at h
    simpa only [show (4 : ℝ) * (2 * L) = 8 * L by ring] using h
  by_cases hleft : x ≤ 1 / ((2 * L) * (m : ℝ))
  · apply htransport 1 (by norm_num)
    intro t ht
    constructor
    · nlinarith [hx.1, ht.1]
    · nlinarith [ht.2]
  · apply htransport (-1) (by norm_num)
    intro t ht
    constructor
    · nlinarith [ht.2]
    · nlinarith [hx.2, ht.1]

end RhAstraSynthesis
