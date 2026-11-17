import RhAstraSynthesis.ReciprocalTaylorRemainder
import RhAstraSynthesis.ReciprocalGevreyMajorant

/-!
# Absolute weighted reciprocal remainder series

The two finite degree regimes are dominated by a single additive majorant.
All degree series start at one. This result concerns real absolute remainders,
not yet the identity with a difference of complex coefficient profiles.
-/

noncomputable section
namespace RhAstraSynthesis

/-- Sum the mixed moments before collapsing the finite Taylor-order sum. -/
lemma reciprocal_mixed_remainder_series (p : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    Summable (fun k : ℕ => ∑ s ∈ Finset.range p,
      (8 : ℝ) ^ s * ((((k + 1 : ℕ) : ℝ) ^ (p + 2 * s) * σ ^ (k + 1)) /
        ((2 * s).factorial : ℝ))) ∧
    (∑' k : ℕ, ∑ s ∈ Finset.range p,
      (8 : ℝ) ^ s * ((((k + 1 : ℕ) : ℝ) ^ (p + 2 * s) * σ ^ (k + 1)) /
        ((2 * s).factorial : ℝ))) ≤
      (8 : ℝ) ^ p * (p.factorial : ℝ) *
        (1 / (1 - σ) * ((1 + 8 / (1 - σ) ^ 2) / (1 - σ)) ^ p) := by
  have hs (s : ℕ) (hs : s ∈ Finset.range p) :=
    (mixed_geometric_gevrey_moment p s (Finset.mem_range.mp hs).le hσ hσ1).1.mul_left
      ((8 : ℝ) ^ s)
  refine ⟨summable_sum hs, ?_⟩
  rw [Summable.tsum_finsetSum hs]
  calc
    _ ≤ ∑ s ∈ Finset.range p, (8 : ℝ) ^ s *
        ((8 : ℝ) ^ p * (p.factorial : ℝ) / (1 - σ) ^ (p + 2 * s + 1)) := by
      apply Finset.sum_le_sum
      intro s hsp
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left
        (mixed_geometric_gevrey_moment p s (Finset.mem_range.mp hsp).le hσ hσ1).2
        (by positivity)
    _ = ((8 : ℝ) ^ p * (p.factorial : ℝ)) *
        ∑ s ∈ Finset.range p, (8 : ℝ) ^ s / (1 - σ) ^ (p + 2 * s + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_mixed_geometric_bound p hσ1)
      (by positivity)

/-- Original sample and degree hypotheses imply convergence and a uniform
Gevrey-1 bound for the absolute weighted real remainder, for every positive
sample index and truncation order. No remainder or convergence hypothesis is used. -/
theorem polynomial_reciprocal_family_remainder_gevrey
    (P : ℕ → Polynomial ℝ) (L n p : ℕ) {C R r : ℝ}
    (hC : 0 < C) (hR : 0 < R) (hr : 0 ≤ r) (hL : 0 < L)
    (hn : 0 < n) (hp : 0 < p)
    (hdegree : ∀ m, 0 < m → (P m).natDegree ≤ m)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m)
    (hσ : (r / R) * Real.exp (2 / Real.sqrt (L : ℝ)) < 1) :
    Summable (fun k : ℕ =>
      |(P (k + 1)).eval (1 / (n : ℝ)) -
        (∑ s ∈ Finset.range p, (P (k + 1)).coeff s * (1 / (n : ℝ)) ^ s)| *
          r ^ (k + 1)) ∧
    (∑' k : ℕ, |(P (k + 1)).eval (1 / (n : ℝ)) -
      (∑ s ∈ Finset.range p, (P (k + 1)).coeff s * (1 / (n : ℝ)) ^ s)| *
        r ^ (k + 1)) ≤
      3 * C / (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) *
        (72 * (L : ℝ) /
          (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ 3) ^ p *
            (p.factorial : ℝ) / (n : ℝ) ^ p := by
  let σ := (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))
  let d := 1 - σ
  have hσ0 : 0 ≤ σ := mul_nonneg (div_nonneg hr hR.le) (Real.exp_pos _).le
  have hd : 0 < d := sub_pos.mpr hσ
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  have hd2 : d ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
  have hnpos : (0 : ℝ) < (n : ℝ) ^ p := by positivity
  let a : ℕ → ℝ := fun k => (n : ℝ) ^ p *
    |(P (k + 1)).eval (1 / (n : ℝ)) -
      (∑ s ∈ Finset.range p, (P (k + 1)).coeff s * (1 / (n : ℝ)) ^ s)| * r ^ (k + 1)
  let S : ℕ → ℝ := fun k => (C * (8 * (L : ℝ)) ^ p / ((2 * p).factorial : ℝ)) *
    (((k + 1 : ℕ) : ℝ) ^ (3 * p) * σ ^ (k + 1))
  let T : ℕ → ℝ := fun k => C * (L : ℝ) ^ p *
    (((k + 1 : ℕ) : ℝ) ^ p * σ ^ (k + 1))
  let U : ℕ → ℝ := fun k => C * (L : ℝ) ^ p *
    ∑ s ∈ Finset.range p, (8 : ℝ) ^ s *
      ((((k + 1 : ℕ) : ℝ) ^ (p + 2 * s) * σ ^ (k + 1)) / ((2 * s).factorial : ℝ))
  have hpoint (k : ℕ) : a k ≤ S k + T k + U k := by
    let m := k + 1
    have hm : 0 < m := Nat.succ_pos k
    have hB : 0 < C * (1 / R) ^ m := by positivity
    have hw := reciprocal_exponential_weight m r R (L : ℝ)
    have he : (1 : ℝ) ≤ Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hweight : C * (1 / R) ^ m * r ^ m ≤ C * σ ^ m := by
      calc
        _ ≤ Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) *
            (C * (1 / R) ^ m * r ^ m) := by
          exact le_mul_of_one_le_left (by positivity) he
        _ = _ := by dsimp [σ]; rw [← hw]; ring
    by_cases hsmall : L * m ≤ n
    · have hb := polynomial_reciprocal_taylor_remainder_bound (P m)
        (C * (1 / R) ^ m) L m n p hB hL hm hn hp hsmall
        (hdegree m hm) (hsample m hm)
      have hb' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb hnpos.le) (pow_nonneg hr m)
      have heq : (n : ℝ) ^ p *
          (Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * (C * (1 / R) ^ m) *
            (8 * (L : ℝ)) ^ p * (m : ℝ) ^ (3 * p) /
              (((2 * p).factorial : ℝ) * (n : ℝ) ^ p)) * r ^ m = S k := by
        dsimp [S]
        rw [← hw]
        dsimp [m]
        field_simp [ne_of_gt hnpos]
        <;> ring
      change a k ≤ _ at hb'
      rw [heq] at hb'
      have ht0 : 0 ≤ T k := by dsimp [T]; positivity
      have hu0 : 0 ≤ U k := by dsimp [U]; positivity
      linarith
    · have hb := polynomial_reciprocal_large_degree_remainder_bound (P m)
        (C * (1 / R) ^ m) L m n p hB hL hm hn (by omega)
        (hdegree m hm) (hsample m hm)
      have hb' := mul_le_mul_of_nonneg_right hb (pow_nonneg hr m)
      have heq : (Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) *
          (C * (1 / R) ^ m) * (L : ℝ) ^ p *
            ∑ s ∈ Finset.range p,
              (8 : ℝ) ^ s * (m : ℝ) ^ (p + 2 * s) / ((2 * s).factorial : ℝ)) * r ^ m = U k := by
        dsimp [U]
        rw [← hw]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        dsimp [m]
        ring
      have ht : (C * (1 / R) ^ m * (L : ℝ) ^ p * (m : ℝ) ^ p) * r ^ m ≤ T k := by
        calc
          _ = (C * (1 / R) ^ m * r ^ m) * ((L : ℝ) ^ p * (m : ℝ) ^ p) := by ring
          _ ≤ (C * σ ^ m) * ((L : ℝ) ^ p * (m : ℝ) ^ p) :=
            mul_le_mul_of_nonneg_right hweight (by positivity)
          _ = T k := by dsimp [T, m]; ring
      change a k ≤ _ at hb'
      rw [add_mul, heq] at hb'
      have hs0 : 0 ≤ S k := by dsimp [S]; positivity
      linarith
  obtain ⟨hS, bS⟩ := cubic_geometric_gevrey_majorant S p hC.le (Nat.cast_nonneg L)
    hσ0 hσ (fun k => by dsimp [S]; positivity) (fun _ => le_rfl)
  obtain ⟨hmoment, bmoment⟩ := geometric_power_moment p hσ0 hσ
  have hT : Summable T := hmoment.mul_left (C * (L : ℝ) ^ p)
  obtain ⟨hmixed, bmixed⟩ := reciprocal_mixed_remainder_series p hσ0 hσ
  have hU : Summable U := hmixed.mul_left (C * (L : ℝ) ^ p)
  let H := C / d * (72 * (L : ℝ) / d ^ 3) ^ p * (p.factorial : ℝ)
  have bS' : (∑' k, S k) ≤ H := by
    apply bS.trans
    change C / d * (64 * (L : ℝ) / d ^ 3) ^ p * _ ≤ H
    dsimp [H]
    gcongr <;> norm_num
  have hbaseT : (L : ℝ) / d ≤ 72 * (L : ℝ) / d ^ 3 := by
    have hLp : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    calc
      _ = ((L : ℝ) * d ^ 2) / d ^ 3 := by
        field_simp [ne_of_gt hd]
        <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (by nlinarith [mul_nonneg hLp (sub_nonneg.mpr hd2)]) (by positivity)
  have hbaseU : 8 * (L : ℝ) * ((1 + 8 / d ^ 2) / d) ≤
      72 * (L : ℝ) / d ^ 3 := by
    have hLp : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    calc
      _ = (8 * (L : ℝ) * (d ^ 2 + 8)) / d ^ 3 := by
        field_simp [ne_of_gt hd]
        <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (by nlinarith [mul_nonneg hLp (sub_nonneg.mpr hd2)]) (by positivity)
  have bT : (∑' k, T k) ≤ H := by
    change (∑' k, C * (L : ℝ) ^ p * _) ≤ _
    rw [tsum_mul_left]
    calc
      _ ≤ C * (L : ℝ) ^ p * ((p.factorial : ℝ) / d ^ (p + 1)) :=
        mul_le_mul_of_nonneg_left bmoment (by positivity)
      _ = C / d * ((L : ℝ) / d) ^ p * (p.factorial : ℝ) := by
        rw [div_pow, pow_succ]; ring
      _ ≤ H := by dsimp [H]; gcongr
  have bU : (∑' k, U k) ≤ H := by
    change (∑' k, C * (L : ℝ) ^ p * _) ≤ _
    rw [tsum_mul_left]
    calc
      _ ≤ C * (L : ℝ) ^ p * ((8 : ℝ) ^ p * (p.factorial : ℝ) *
          (1 / d * ((1 + 8 / d ^ 2) / d) ^ p)) :=
        mul_le_mul_of_nonneg_left bmixed (by positivity)
      _ = C / d * (8 * (L : ℝ) * ((1 + 8 / d ^ 2) / d)) ^ p *
          (p.factorial : ℝ) := by simp only [mul_pow]; ring
      _ ≤ H := by dsimp [H]; gcongr
  have hmajor : Summable (fun k => S k + T k + U k) := (hS.add hT).add hU
  have ha : Summable a := Summable.of_nonneg_of_le
    (fun k => by dsimp [a]; positivity) hpoint hmajor
  have ba : (∑' k, a k) ≤ 3 * H := by
    have hb := ha.tsum_le_tsum hpoint hmajor
    rw [(hS.add hT).tsum_add hU, hS.tsum_add hT] at hb
    linarith
  have heq (k : ℕ) : a k / (n : ℝ) ^ p =
      |(P (k + 1)).eval (1 / (n : ℝ)) -
        (∑ s ∈ Finset.range p, (P (k + 1)).coeff s * (1 / (n : ℝ)) ^ s)| *
          r ^ (k + 1) := by
    dsimp [a]
    field_simp [ne_of_gt hnpos]
    <;> ring
  refine ⟨(ha.div_const ((n : ℝ) ^ p)).congr heq, ?_⟩
  simp_rw [← heq]
  rw [tsum_div_const]
  calc
    _ ≤ (3 * H) / (n : ℝ) ^ p := div_le_div_of_nonneg_right ba hnpos.le
    _ = _ := by dsimp [H, d, σ]; ring

end RhAstraSynthesis
