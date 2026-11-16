import RhAstraSynthesis.TentMultiplier
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Critical-Line Gap and Non-Outer Off-Axis Zeros of the Tent Mellin Multiplier

Formalizes the Hardy–Mellin obstruction of `TentMultiplier`:
1. Sharp quantitative critical-line lower bound
   `√3 - 1 - 1 / √2 ≤ ‖TentMultiplier.numerator s‖` for all `s` with `Re(s) = 1/2`;
2. Constructive Banach fixed-point proof (`ContractingWith.exists_fixedPoint'`) that
   `TentMultiplier.numerator s = 0` possesses infinitely many zeros in the right half-plane
   `2 < Re(s) < 4` with arbitrarily large imaginary part (`R < Im(s)`), proving that
   the tent Mellin multiplier `M_τ` fails to be an outer function in `H²(C_{1/2}^+)`.
-/

namespace RhAstraSynthesis

open Complex Metric

/-- On the entire critical line `Re(s) = 1/2`, the tent numerator is bounded uniformly
away from zero by `√3 - 1 - 1 / √2 > 0`. -/
theorem tent_numerator_half_line_lower_bound :
    0 < Real.sqrt 3 - 1 - 1 / Real.sqrt 2 ∧
      ∀ s : ℂ, s.re = 1 / 2 →
        Real.sqrt 3 - 1 - 1 / Real.sqrt 2 ≤ ‖TentMultiplier.numerator s‖ := by
  have hsq2_pos : 0 < Real.sqrt 2 := by positivity
  have hsq2_lt : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsum_sq : (1 + 1 / Real.sqrt 2) ^ 2 < 3 := by
    have hinv_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    have hmul : 2 * (1 / Real.sqrt 2) = Real.sqrt 2 := by
      field_simp [hsq2_pos.ne']
      rw [Real.sq_sqrt (by norm_num)]
    calc
      (1 + 1 / Real.sqrt 2) ^ 2 = 1 + 2 * (1 / Real.sqrt 2) + (1 / Real.sqrt 2) ^ 2 := by ring
      _ = 3 / 2 + Real.sqrt 2 := by rw [hmul, hinv_sq]; ring
      _ < 3 := by linarith
  have hpos : 0 < Real.sqrt 3 - 1 - 1 / Real.sqrt 2 := by
    have hlt : 1 + 1 / Real.sqrt 2 < Real.sqrt 3 := (Real.lt_sqrt (by positivity)).mpr hsum_sq
    linarith
  refine ⟨hpos, fun s hs => ?_⟩
  have hre : s.re - 1 = -(1 / 2 : ℝ) := by linarith
  have h2_norm : ‖(2 : ℂ) ^ (s - 1)‖ = 1 / Real.sqrt 2 := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) (s - 1)
    simp only [Complex.ofReal_ofNat, Complex.sub_re, Complex.one_re, hre] at h
    rw [h, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]
  have h43_norm : ‖(2 : ℂ) * ((4 / 3 : ℝ) : ℂ) ^ (s - 1)‖ = Real.sqrt 3 := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (x := (4 / 3 : ℝ)) (by norm_num) (s - 1)
    simp only [Complex.sub_re, Complex.one_re, hre] at h
    rw [norm_mul, h, show (‖(2 : ℂ)‖ : ℝ) = 2 by norm_num, Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow]
    have h43_sq : Real.sqrt (4 / 3 : ℝ) = 2 / Real.sqrt 3 := by
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [Real.sqrt_div (by norm_num), h4]
    rw [h43_sq]
    have hsq3_pos : 0 < Real.sqrt 3 := by positivity
    field_simp [hsq3_pos.ne']
  have h12_norm : ‖(1 : ℂ) + (2 : ℂ) ^ (s - 1)‖ ≤ 1 + 1 / Real.sqrt 2 := by
    calc
      ‖(1 : ℂ) + (2 : ℂ) ^ (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (s - 1)‖ := norm_add_le _ _
      _ = 1 + 1 / Real.sqrt 2 := by rw [h2_norm]; norm_num
  unfold TentMultiplier.numerator
  rw [norm_sub_rev]
  have hlow := norm_sub_norm_le (2 * ((4 / 3 : ℝ) : ℂ) ^ (s - 1)) ((1 : ℂ) + (2 : ℂ) ^ (s - 1))
  rw [h43_norm] at hlow
  linarith [hlow, h12_norm]

section OffAxisZeros

private noncomputable def aLog : ℝ := Real.log (3 / 2)
private noncomputable def bLog : ℝ := Real.log 2
private noncomputable def sig0 : ℝ := bLog / aLog
private noncomputable def tPer : ℝ := 2 * Real.pi / aLog

private lemma aLog_bounds : (2 / 5 : ℝ) < aLog ∧ aLog < 1 / 2 := by
  have he_lt : Real.exp 1 < 11 / 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he_gt : (27 / 10 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he2_eq : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he2_lt : Real.exp 2 < (3 / 2 : ℝ) ^ 5 := by
    rw [he2_eq]
    calc
      (Real.exp 1) ^ 2 < (11 / 4 : ℝ) ^ 2 := by gcongr
      _ < (3 / 2 : ℝ) ^ 5 := by norm_num
  have h_gt : 2 / 5 < aLog := by
    have hlog := Real.log_lt_log (Real.exp_pos 2) he2_lt
    rw [Real.log_exp, Real.log_pow] at hlog
    change 2 < 5 * aLog at hlog
    linarith
  have he1_gt : (3 / 2 : ℝ) ^ 2 < Real.exp 1 := by
    calc
      (3 / 2 : ℝ) ^ 2 < (27 / 10 : ℝ) := by norm_num
      _ < Real.exp 1 := he_gt
  have h_lt : aLog < 1 / 2 := by
    have hlog := Real.log_lt_log (by norm_num) he1_gt
    rw [Real.log_exp, Real.log_pow] at hlog
    change 2 * aLog < 1 at hlog
    linarith
  exact ⟨h_gt, h_lt⟩

private lemma bLog_pos : 0 < bLog := Real.log_pos (by norm_num)

private lemma aLog_pos : 0 < aLog := by linarith [aLog_bounds.1]

private lemma sig0_lt_twelve_div_seven : sig0 < 12 / 7 := by
  have hpow : (2 : ℝ) ^ 7 < (3 / 2 : ℝ) ^ 12 := by norm_num
  have hlog := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  change 7 * bLog < 12 * aLog at hlog
  unfold sig0
  rw [div_lt_iff₀ aLog_pos]
  linarith

private lemma step31_delta_bounds :
    (1 / 300 : ℝ) < 53 - 31 * sig0 ∧ 53 - 31 * sig0 < 1 / 160 := by
  have hlow_rat : (491 / 490 : ℝ) < (3 / 2 : ℝ) ^ 53 / (2 : ℝ) ^ 31 := by
    rw [lt_div_iff₀ (by positivity)]
    norm_num
  have hhigh_rat : (3 / 2 : ℝ) ^ 53 / (2 : ℝ) ^ 31 < 471 / 470 := by
    rw [div_lt_iff₀ (by positivity)]
    norm_num
  have hlog_ratio :
      Real.log ((3 / 2 : ℝ) ^ 53 / (2 : ℝ) ^ 31) = 53 * aLog - 31 * bLog := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rfl
  have hlow_log : (1 / 491 : ℝ) < 53 * aLog - 31 * bLog := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 491 / 490 by norm_num)
    have h2 : Real.log (491 / 490 : ℝ) < 53 * aLog - 31 * bLog := by
      rw [← hlog_ratio]
      exact Real.log_lt_log (by norm_num) hlow_rat
    linarith [h1, h2, show (1 - (491 / 490 : ℝ)⁻¹ : ℝ) = 1 / 491 by norm_num]
  have hhigh_log : 53 * aLog - 31 * bLog < 1 / 470 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 471 / 470 by norm_num)
    have h2 : 53 * aLog - 31 * bLog < Real.log (471 / 470 : ℝ) := by
      rw [← hlog_ratio]
      exact Real.log_lt_log (by positivity) hhigh_rat
    linarith [h1, h2, show ((471 / 470 : ℝ) - 1 : ℝ) = 1 / 470 by norm_num]
  have ha := aLog_bounds
  have hdelta_eq : 53 - 31 * sig0 = (53 * aLog - 31 * bLog) / aLog := by
    unfold sig0
    field_simp [aLog_pos.ne']
  rw [hdelta_eq]
  constructor
  · rw [lt_div_iff₀ aLog_pos]
    nlinarith [ha.2, hlow_log]
  · rw [div_lt_iff₀ aLog_pos]
    nlinarith [ha.1, hhigh_log]

private noncomputable def gapMeasure (n : ℕ) : ℝ :=
  let x := Int.fract ((n : ℝ) * sig0)
  if (0.505 : ℝ) < x then x - 0.505 else x + 0.495

/-- Finite-step sweep: starting from any `k0 : ℕ`, some `k = k0 + 31 * j` (`j ≤ 301`)
has `Int.fract (k * sig0) ∈ [0.495, 0.505]`. -/
private lemma exists_good_multiple (k0 : ℕ) :
    ∃ k : ℕ, k0 ≤ k ∧ Int.fract ((k : ℝ) * sig0) ∈ Set.Icc (0.495 : ℝ) (0.505 : ℝ) := by
  let δ : ℝ := 53 - 31 * sig0
  have hδ := step31_delta_bounds
  have hstep_fract : ∀ n : ℕ,
      Int.fract (((n + 31 : ℕ) : ℝ) * sig0) =
        if δ ≤ Int.fract ((n : ℝ) * sig0) then Int.fract ((n : ℝ) * sig0) - δ
        else Int.fract ((n : ℝ) * sig0) + 1 - δ := by
    intro n
    have heq : ((n + 31 : ℕ) : ℝ) * sig0 = (n : ℝ) * sig0 + 53 - δ := by
      push_cast
      dsimp [δ]
      ring
    rw [heq]
    have hfr0 := Int.fract_nonneg ((n : ℝ) * sig0)
    have hfr1 := Int.fract_lt_one ((n : ℝ) * sig0)
    have hadd53 :
        (n : ℝ) * sig0 + 53 - δ =
          ((⌊(n : ℝ) * sig0⌋ + 53 : ℤ) : ℝ) + (Int.fract ((n : ℝ) * sig0) - δ) := by
      have hdecomp := Int.floor_add_fract ((n : ℝ) * sig0)
      push_cast
      linarith
    split_ifs with hle
    · have hin : Int.fract ((n : ℝ) * sig0) - δ ∈ Set.Ico (0 : ℝ) 1 :=
        ⟨by linarith, by linarith [hδ.1]⟩
      rw [hadd53, Int.fract_intCast_add]
      exact Int.fract_eq_self.mpr hin
    · have hlt : Int.fract ((n : ℝ) * sig0) < δ := lt_of_not_ge hle
      have hadd52 :
          (n : ℝ) * sig0 + 53 - δ =
            ((⌊(n : ℝ) * sig0⌋ + 52 : ℤ) : ℝ) + (Int.fract ((n : ℝ) * sig0) + 1 - δ) := by
        have hdecomp := Int.floor_add_fract ((n : ℝ) * sig0)
        push_cast
        linarith
      have hin : Int.fract ((n : ℝ) * sig0) + 1 - δ ∈ Set.Ico (0 : ℝ) 1 :=
        ⟨by linarith [hδ.2], by linarith⟩
      rw [hadd52, Int.fract_intCast_add]
      exact Int.fract_eq_self.mpr hin
  have haux :
      ∀ (m n : ℕ),
        gapMeasure n ≤ (m : ℝ) * (1 / 300 : ℝ) →
        ∃ j ≤ m, Int.fract (((n + 31 * j : ℕ) : ℝ) * sig0) ∈ Set.Icc (0.495 : ℝ) (0.505 : ℝ) := by
    intro m
    induction m with
    | zero =>
        intro n hm
        simp only [Nat.cast_zero, zero_mul, gapMeasure] at hm
        have hx0 := Int.fract_nonneg ((n : ℝ) * sig0)
        split_ifs at hm <;> linarith
    | succ m ih =>
        intro n hm
        let x := Int.fract ((n : ℝ) * sig0)
        by_cases hin : x ∈ Set.Icc (0.495 : ℝ) (0.505 : ℝ)
        · exact ⟨0, Nat.zero_le _, by simpa using hin⟩
        · have hs := hstep_fract n
          have hm' : (if (0.505 : ℝ) < x then x - 0.505 else x + 0.495) ≤
              ((m : ℝ) + 1) * (1 / 300 : ℝ) := by
            simpa [gapMeasure, x, Nat.cast_add, Nat.cast_one] using hm
          by_cases hhi : (0.505 : ℝ) < x
          · rw [ite_eq_left_iff.mpr (fun h => absurd hhi h)] at hm'
            have hδ_le : δ ≤ x := by linarith [hδ.2]
            have hx1 : Int.fract (((n + 31 : ℕ) : ℝ) * sig0) = x - δ := by
              rw [hs]
              exact ite_eq_left_iff.mpr (fun h => absurd hδ_le h)
            by_cases hhit : x - δ ∈ Set.Icc (0.495 : ℝ) (0.505 : ℝ)
            · rw [← hx1] at hhit
              exact ⟨1, by omega, hhit⟩
            · have hhi1 : (0.505 : ℝ) < x - δ := by
                by_contra hnot
                exact hhit ⟨by linarith [hδ.2], le_of_not_gt hnot⟩
              have hnext : gapMeasure (n + 31) ≤ (m : ℝ) * (1 / 300 : ℝ) := by
                dsimp [gapMeasure]
                rw [hx1, ite_eq_left_iff.mpr (fun h => absurd hhi1 h)]
                linarith [hδ.1]
              obtain ⟨j, hj, hres⟩ := ih (n + 31) hnext
              refine ⟨j + 1, by omega, ?_⟩
              simpa [show n + 31 * (j + 1) = (n + 31) + 31 * j by omega] using hres
          · rw [ite_eq_right_iff.mpr (fun h => absurd h hhi)] at hm'
            have hx_lt : x < 0.495 := by
              by_contra hnot
              exact hin ⟨le_of_not_gt hnot, le_of_not_gt hhi⟩
            have hx0 : 0 ≤ x := Int.fract_nonneg _
            by_cases hδ_le : δ ≤ x
            · have hx1 : Int.fract (((n + 31 : ℕ) : ℝ) * sig0) = x - δ := by
                rw [hs]
                exact ite_eq_left_iff.mpr (fun h => absurd hδ_le h)
              have hhi1 : ¬ (0.505 : ℝ) < x - δ := by linarith [hδ.1]
              have hnext : gapMeasure (n + 31) ≤ (m : ℝ) * (1 / 300 : ℝ) := by
                dsimp [gapMeasure]
                rw [hx1, ite_eq_right_iff.mpr (fun h => absurd h hhi1)]
                linarith [hδ.1]
              obtain ⟨j, hj, hres⟩ := ih (n + 31) hnext
              refine ⟨j + 1, by omega, ?_⟩
              simpa [show n + 31 * (j + 1) = (n + 31) + 31 * j by omega] using hres
            · have hx1 : Int.fract (((n + 31 : ℕ) : ℝ) * sig0) = x + 1 - δ := by
                rw [hs]
                exact ite_eq_right_iff.mpr (fun h => absurd h hδ_le)
              have hhi1 : (0.505 : ℝ) < x + 1 - δ := by linarith [hx0, hδ.2]
              have hnext : gapMeasure (n + 31) ≤ (m : ℝ) * (1 / 300 : ℝ) := by
                dsimp [gapMeasure]
                rw [hx1, ite_eq_left_iff.mpr (fun h => absurd hhi1 h)]
                linarith [hδ.1]
              obtain ⟨j, hj, hres⟩ := ih (n + 31) hnext
              refine ⟨j + 1, by omega, ?_⟩
              simpa [show n + 31 * (j + 1) = (n + 31) + 31 * j by omega] using hres
  have hm_init : gapMeasure k0 ≤ (301 : ℕ) * (1 / 300 : ℝ) := by
    have hx0 := Int.fract_nonneg ((k0 : ℝ) * sig0)
    have hx1 := Int.fract_lt_one ((k0 : ℝ) * sig0)
    dsimp [gapMeasure]
    split_ifs <;> norm_num <;> linarith
  obtain ⟨j, _, hj⟩ := haux 301 k0 hm_init
  exact ⟨k0 + 31 * j, Nat.le_add_right _ _, hj⟩

private noncomputable def phiMap (k : ℕ) (w : ℂ) : ℂ :=
  (sig0 : ℂ) + ((k : ℝ) * tPer : ℂ) * I -
    Complex.log (1 + Complex.exp (-w * (bLog : ℂ))) / (aLog : ℂ)

private lemma rpow_neg_seven_fourths_lt : (2 : ℝ) ^ (-(7 / 4 : ℝ)) < 3 / 10 := by
  have hpow : ((2 : ℝ) ^ (-(7 / 4 : ℝ))) ^ (4 : ℕ) < (3 / 10 : ℝ) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(7 / 4 : ℝ))) 4, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    (by norm_num : 4 ≠ 0)).mp hpow

private lemma rpow_neg_nine_fourths_bounds :
    (1 / 5 : ℝ) < (2 : ℝ) ^ (-(9 / 4 : ℝ)) ∧ (2 : ℝ) ^ (-(9 / 4 : ℝ)) < 5 / 23 := by
  have hlow : (1 / 5 : ℝ) ^ (4 : ℕ) < ((2 : ℝ) ^ (-(9 / 4 : ℝ))) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(9 / 4 : ℝ))) 4, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hhigh : ((2 : ℝ) ^ (-(9 / 4 : ℝ))) ^ (4 : ℕ) < (5 / 23 : ℝ) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(9 / 4 : ℝ))) 4, ← Real.rpow_mul (by norm_num)]
    norm_num
  constructor
  · exact (pow_lt_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (by norm_num : 4 ≠ 0)).mp hlow
  · exact (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (by norm_num : 4 ≠ 0)).mp hhigh

private lemma exp_neg_mul_bLog_norm_lt {w : ℂ} (hw : (7 / 4 : ℝ) ≤ w.re) :
    ‖Complex.exp (-w * (bLog : ℂ))‖ < 3 / 10 := by
  have hre : (-w * (bLog : ℂ)).re = -w.re * bLog := by
    simp [Complex.mul_re]
  rw [Complex.norm_exp, hre]
  have h2pow : Real.exp (-w.re * bLog) = (2 : ℝ) ^ (-w.re) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [bLog]
    ring
  rw [h2pow]
  have hmono : (2 : ℝ) ^ (-w.re) ≤ (2 : ℝ) ^ (-(7 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact lt_of_le_of_lt hmono rpow_neg_seven_fourths_lt

private lemma phiMap_hasDerivAt {k : ℕ} {w : ℂ} (hw : (7 / 4 : ℝ) ≤ w.re) :
    HasDerivAt (phiMap k)
      ((bLog : ℂ) / (aLog : ℂ) *
        (Complex.exp (-w * (bLog : ℂ)) / (1 + Complex.exp (-w * (bLog : ℂ))))) w := by
  have hnorm := exp_neg_mul_bLog_norm_lt hw
  have hre_pos : 0 < (1 + Complex.exp (-w * (bLog : ℂ))).re := by
    have hre_le : ‖Complex.exp (-w * (bLog : ℂ))‖ ≤ 3 / 10 := hnorm.le
    have habs := (Complex.abs_re_le_norm (Complex.exp (-w * (bLog : ℂ)))).trans hre_le
    have hneg : -(3 / 10 : ℝ) ≤ (Complex.exp (-w * (bLog : ℂ))).re := (abs_le.mp habs).1
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hslit : 1 + Complex.exp (-w * (bLog : ℂ)) ∈ Complex.slitPlane :=
    Or.inl hre_pos
  have hexp_d : HasDerivAt (fun z : ℂ => 1 + Complex.exp (-z * (bLog : ℂ)))
      (Complex.exp (-w * (bLog : ℂ)) * -(bLog : ℂ)) w := by
    have hlin : HasDerivAt (fun z : ℂ => -z * (bLog : ℂ)) (-(bLog : ℂ)) w := by
      simpa using ((hasDerivAt_id w).neg).mul_const (bLog : ℂ)
    exact (hlin.cexp).const_add 1
  have hlog_d := hexp_d.clog hslit
  have hconst_d : HasDerivAt (fun _ : ℂ => (sig0 : ℂ) + ((k : ℝ) * tPer : ℂ) * I) 0 w :=
    hasDerivAt_const _ _
  have hdiv_d := hlog_d.div_const (aLog : ℂ)
  have hsub_d := hconst_d.sub hdiv_d
  have ha_ne : (aLog : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr aLog_pos.ne'
  have hfun_eq : (fun x : ℂ => (sig0 : ℂ) + ((k : ℝ) * tPer : ℂ) * I -
      Complex.log (1 + Complex.exp (-x * (bLog : ℂ))) / (aLog : ℂ)) = phiMap k := rfl
  have hval_eq :
      0 - Complex.exp (-w * (bLog : ℂ)) * -(bLog : ℂ) / (1 + Complex.exp (-w * (bLog : ℂ))) / (aLog : ℂ) =
        (bLog : ℂ) / (aLog : ℂ) *
          (Complex.exp (-w * (bLog : ℂ)) / (1 + Complex.exp (-w * (bLog : ℂ)))) := by
    field_simp [ha_ne]
    ring
  rw [← hfun_eq, ← hval_eq]
  exact hsub_d

private lemma phiMap_norm_deriv_le {k : ℕ} {w : ℂ} (hw : (7 / 4 : ℝ) ≤ w.re) :
    ‖deriv (phiMap k) w‖ ≤ 36 / 49 := by
  rw [(phiMap_hasDerivAt hw).deriv]
  have hu := exp_neg_mul_bLog_norm_lt hw
  have hden : (7 / 10 : ℝ) ≤ ‖1 + Complex.exp (-w * (bLog : ℂ))‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (-Complex.exp (-w * (bLog : ℂ)))
    rw [norm_one, norm_neg, sub_neg_eq_add] at htri
    linarith
  have hfrac_ba : ‖(bLog : ℂ) / (aLog : ℂ)‖ ≤ 12 / 7 := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg bLog_pos.le,
      Real.norm_of_nonneg aLog_pos.le]
    exact sig0_lt_twelve_div_seven.le
  have hden_pos : 0 < ‖1 + Complex.exp (-w * (bLog : ℂ))‖ := by linarith
  have hratio :
      ‖Complex.exp (-w * (bLog : ℂ)) / (1 + Complex.exp (-w * (bLog : ℂ)))‖ ≤ 3 / 7 := by
    rw [norm_div]
    calc
      ‖Complex.exp (-w * (bLog : ℂ))‖ / ‖1 + Complex.exp (-w * (bLog : ℂ))‖
          ≤ (3 / 10 : ℝ) / (7 / 10 : ℝ) :=
        div_le_div₀ (by positivity) hu.le (by norm_num) hden
      _ = 3 / 7 := by norm_num
  rw [norm_mul]
  calc
    ‖(bLog : ℂ) / (aLog : ℂ)‖ *
        ‖Complex.exp (-w * (bLog : ℂ)) / (1 + Complex.exp (-w * (bLog : ℂ)))‖
        ≤ (12 / 7 : ℝ) * (3 / 7 : ℝ) :=
      mul_le_mul hfrac_ba hratio (norm_nonneg _) (by norm_num)
    _ = 36 / 49 := by norm_num

private lemma phiMap_center_dist_le (k : ℕ)
    (hk : Int.fract ((k : ℝ) * sig0) ∈ Set.Icc (0.495 : ℝ) (0.505 : ℝ)) :
    let c : ℂ := ((9 / 4 : ℝ) : ℂ) + ((k : ℝ) * tPer : ℂ) * I
    ‖phiMap k c - c‖ ≤ 13 / 98 := by
  intro c
  let u : ℂ := Complex.exp (-c * (bLog : ℂ))
  let u0 : ℝ := -((2 : ℝ) ^ (-(9 / 4 : ℝ)))
  have hu0_bounds := rpow_neg_nine_fourths_bounds
  have hphi_split :
      phiMap k c - c =
        ((((sig0 - Real.log (1 + u0) / aLog - 9 / 4 : ℝ) : ℂ)) -
          (Complex.log (1 + u) - Complex.log (1 + (u0 : ℂ))) / (aLog : ℂ)) := by
    unfold phiMap u
    have hu0_pos : 0 < 1 + u0 := by dsimp [u0]; linarith
    have hlog_real : ((Real.log (1 + u0) : ℝ) : ℂ) = Complex.log ((1 + u0 : ℝ) : ℂ) :=
      Complex.ofReal_log hu0_pos.le
    push_cast [c]
    rw [hlog_real]
    simp only [Complex.ofReal_add, Complex.ofReal_one]
    have ha_ne : (aLog : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr aLog_pos.ne'
    field_simp [ha_ne]
    ring
  -- 1. Real center residual `|sig0 - log(1 + u0)/aLog - 9/4| ≤ 3/40`
  have hreal_bound : |sig0 - Real.log (1 + u0) / aLog - 9 / 4| ≤ 3 / 40 := by
    let R : ℝ := 2 / ((1 + u0) * (3 / 2 : ℝ) ^ (9 / 4 : ℝ))
    have hu0_pos : 0 < 1 + u0 := by dsimp [u0]; linarith
    have hR_pos : 0 < R := by positivity
    have h32_9 : ((3 / 2 : ℝ) ^ (9 / 4 : ℝ)) ^ (4 : ℕ) = (3 / 2 : ℝ) ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast ((3 / 2 : ℝ) ^ (9 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hR4_gt1 : 1 < R ^ (4 : ℕ) := by
      have hsub_lt : 1 + u0 < 4 / 5 := by dsimp [u0]; linarith
      have hdenom_lt : ((1 + u0) * (3 / 2 : ℝ) ^ (9 / 4 : ℝ)) ^ (4 : ℕ) < 16 := by
        rw [mul_pow, h32_9]
        have hp1 : (1 + u0) ^ (4 : ℕ) < (4 / 5 : ℝ) ^ (4 : ℕ) :=
          pow_lt_pow_left₀ hsub_lt hu0_pos.le (by norm_num)
        nlinarith [show (4 / 5 : ℝ) ^ (4 : ℕ) * (3 / 2 : ℝ) ^ (9 : ℕ) < 16 by norm_num]
      dsimp [R]
      rw [div_pow, show (2 : ℝ) ^ (4 : ℕ) = 16 by norm_num, one_lt_div (by positivity)]
      exact hdenom_lt
    have hR_gt1 : 1 < R := by
      by_contra hle
      have : R ^ (4 : ℕ) ≤ 1 ^ (4 : ℕ) := pow_le_pow_left₀ hR_pos.le (le_of_not_gt hle) 4
      linarith
    have hR4_lt : R ^ (4 : ℕ) < (103 / 100 : ℝ) ^ (4 : ℕ) := by
      have hsub_gt : (18 / 23 : ℝ) < 1 + u0 := by dsimp [u0]; linarith
      have hdenom_gt : (18 / 23 : ℝ) ^ (4 : ℕ) * (3 / 2 : ℝ) ^ (9 : ℕ) <
          ((1 + u0) * (3 / 2 : ℝ) ^ (9 / 4 : ℝ)) ^ (4 : ℕ) := by
        rw [mul_pow, h32_9]
        have hp1 : (18 / 23 : ℝ) ^ (4 : ℕ) < (1 + u0) ^ (4 : ℕ) :=
          pow_lt_pow_left₀ hsub_gt (by norm_num) (by norm_num)
        exact mul_lt_mul_of_pos_right hp1 (by positivity)
      dsimp [R]
      rw [div_pow, show (2 : ℝ) ^ (4 : ℕ) = 16 by norm_num, div_lt_iff₀ (by positivity)]
      have hnum : (16 : ℝ) < (103 / 100 : ℝ) ^ (4 : ℕ) * ((18 / 23 : ℝ) ^ (4 : ℕ) * (3 / 2 : ℝ) ^ (9 : ℕ)) := by
        norm_num
      nlinarith [show 0 < (103 / 100 : ℝ) ^ (4 : ℕ) by positivity]
    have hR_lt : R < 103 / 100 :=
      (pow_lt_pow_iff_left₀ hR_pos.le (by norm_num) (by norm_num : 4 ≠ 0)).mp hR4_lt
    have hlog_R : Real.log R = bLog - Real.log (1 + u0) - (9 / 4 : ℝ) * aLog := by
      dsimp [R]
      rw [Real.log_div (by norm_num) (by positivity), Real.log_mul hu0_pos.ne' (by positivity),
        Real.log_rpow (by norm_num)]
      dsimp [aLog, bLog]
      ring
    have hlog_bounds : 0 < Real.log R ∧ Real.log R ≤ 3 / 100 := by
      refine ⟨Real.log_pos hR_gt1, ?_⟩
      exact le_trans (Real.log_le_sub_one_of_pos hR_pos) (by linarith)
    have hdiff_eq : sig0 - Real.log (1 + u0) / aLog - 9 / 4 = Real.log R / aLog := by
      rw [hlog_R]
      unfold sig0
      field_simp [aLog_pos.ne']
    rw [hdiff_eq, abs_of_nonneg (div_nonneg hlog_bounds.1.le aLog_pos.le),
      div_le_iff₀ aLog_pos]
    nlinarith [aLog_bounds.1, hlog_bounds.2]
  -- 2. Phase deviation bound `‖u - u0‖ ≤ 1 / 138`
  have hu_diff : ‖u - (u0 : ℂ)‖ ≤ 1 / 138 := by
    let φ : ℝ := Int.fract ((k : ℝ) * sig0)
    let mFloor : ℤ := ⌊(k : ℝ) * sig0⌋
    have hφ0 : (0.495 : ℝ) ≤ φ := hk.1
    have hφ1 : φ ≤ 0.505 := hk.2
    have hktb : (k : ℝ) * tPer * bLog = 2 * Real.pi * ((k : ℝ) * sig0) := by
      unfold tPer sig0
      ring
    have hk_sig : (k : ℝ) * sig0 = (mFloor : ℝ) + φ :=
      (Int.floor_add_fract ((k : ℝ) * sig0)).symm
    have harg_eq : -c * (bLog : ℂ) =
        ((-(9 / 4 : ℝ) * bLog : ℝ) : ℂ) - ((mFloor : ℝ) * (2 * Real.pi) : ℂ) * I -
          ((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I - (Real.pi : ℂ) * I := by
      have hc_mul : (-c * (bLog : ℂ)) =
          ((-(9 / 4 : ℝ) * bLog : ℝ) : ℂ) - ((((k : ℝ) * tPer * bLog : ℝ) : ℂ) * I) := by
        dsimp [c]
        push_cast
        ring
      have hktb_real : (k : ℝ) * tPer * bLog = 2 * Real.pi * ((mFloor : ℝ) + φ) := by
        rw [hktb, hk_sig]
      have hktb_c : (((k : ℝ) * tPer * bLog : ℝ) : ℂ) =
          ((2 * Real.pi : ℝ) : ℂ) * (((mFloor : ℝ) : ℂ) + (φ : ℂ)) := by
        rw [hktb_real]
        push_cast
        ring
      rw [hc_mul, hktb_c]
      push_cast
      ring
    have hu_eq : u = (u0 : ℂ) * Complex.exp (-((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I) := by
      dsimp [u]
      rw [harg_eq]
      have h1 : Complex.exp
          (((-(9 / 4 : ℝ) * bLog : ℝ) : ℂ) - ((mFloor : ℝ) * (2 * Real.pi) : ℂ) * I -
            ((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I - (Real.pi : ℂ) * I) =
          Complex.exp ((-(9 / 4 : ℝ) * bLog : ℝ) : ℂ) *
            Complex.exp (((-mFloor : ℤ) : ℂ) * (2 * Real.pi * I)) *
            Complex.exp (-(Real.pi * I)) *
            Complex.exp (-((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        push_cast
        ring_nf
      rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_neg, Complex.exp_pi_mul_I]
      have hreal2 : Complex.exp ((-(9 / 4 : ℝ) * bLog : ℝ) : ℂ) =
          (((2 : ℝ) ^ (-(9 / 4 : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_exp, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1
        dsimp [bLog]
        ring
      rw [hreal2]
      simp [u0]
    have hphase_le : ‖Complex.exp (-((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I) - 1‖ ≤
        |2 * Real.pi * (φ - 1 / 2)| := by
      let g : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * I)
      have hg_deriv : ∀ θ : ℝ, HasDerivAt g (Complex.exp ((θ : ℂ) * I) * I) θ := by
        intro θ
        have h := ((hasDerivAt_id (θ : ℂ)).mul_const I).cexp
        simpa [g] using h.comp_ofReal
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun θ _ => (hg_deriv θ).differentiableAt)
        (fun θ _ => by rw [(hg_deriv θ).deriv, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_exp_ofReal_mul_I])
        convex_univ (Set.mem_univ 0) (Set.mem_univ (-(2 * Real.pi * (φ - 1 / 2))))
      simpa [g, abs_neg] using hmvt
    have htheta_bound : |2 * Real.pi * (φ - 1 / 2)| ≤ 315 / 10000 := by
      have hpi : Real.pi < 315 / 100 := lt_trans Real.pi_lt_d4 (by norm_num)
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      have hdiff : |φ - 1 / 2| ≤ 5 / 1000 := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_mul, abs_of_pos (mul_pos (by norm_num) hpi_pos)]
      nlinarith
    rw [hu_eq, show (u0 : ℂ) * Complex.exp (-((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I) - (u0 : ℂ) =
        (u0 : ℂ) * (Complex.exp (-((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I) - 1) by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hu0_abs : |u0| < 5 / 23 := by
      dsimp [u0]
      rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
      exact hu0_bounds.2
    calc
      |u0| * ‖Complex.exp (-((2 * Real.pi * (φ - 1 / 2) : ℝ) : ℂ) * I) - 1‖
          ≤ (5 / 23 : ℝ) * (315 / 10000 : ℝ) :=
        mul_le_mul hu0_abs.le (hphase_le.trans htheta_bound) (norm_nonneg _) (by norm_num)
      _ ≤ 1 / 138 := by norm_num
  -- 3. Apply MVT to `z ↦ Complex.log (1 + z)` on `closedBall 0 (3 / 10)`
  have hu_ball : u ∈ closedBall (0 : ℂ) (3 / 10) := by
    rw [mem_closedBall, dist_zero_right]
    have hc_re : (7 / 4 : ℝ) ≤ c.re := by
      dsimp [c]
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero]
      norm_num
    exact (exp_neg_mul_bLog_norm_lt hc_re).le
  have hu0_ball : (u0 : ℂ) ∈ closedBall (0 : ℂ) (3 / 10) := by
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    dsimp [u0]
    rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    linarith [hu0_bounds.2]
  have hlog_diff : ‖Complex.log (1 + u) - Complex.log (1 + (u0 : ℂ))‖ ≤ (10 / 7) * (1 / 138) := by
    have hdiff : ∀ z ∈ closedBall (0 : ℂ) (3 / 10),
        HasDerivAt (fun w : ℂ => Complex.log (1 + w)) ((1 + z)⁻¹) z := by
      intro z hz
      rw [mem_closedBall, dist_zero_right] at hz
      have hre : 0 < (1 + z).re := by
        have := (abs_le.mp ((Complex.abs_re_le_norm z).trans hz)).1
        simp only [Complex.add_re, Complex.one_re]
        linarith
      simpa [one_div] using ((hasDerivAt_id z).const_add 1).clog (Or.inl hre)
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hdiff z hz).differentiableAt)
      (fun z hz => by
        rw [(hdiff z hz).deriv, norm_inv]
        rw [mem_closedBall, dist_zero_right] at hz
        have hden : (7 / 10 : ℝ) ≤ ‖1 + z‖ := by
          have htri := norm_sub_norm_le (1 : ℂ) (-z)
          rw [norm_one, norm_neg, sub_neg_eq_add] at htri
          linarith
        simpa [inv_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 7 / 10) hden)
      (convex_closedBall (0 : ℂ) (3 / 10)) hu0_ball hu_ball
    calc
      ‖Complex.log (1 + u) - Complex.log (1 + (u0 : ℂ))‖
          ≤ (10 / 7 : ℝ) * ‖u - (u0 : ℂ)‖ := hmvt
      _ ≤ (10 / 7 : ℝ) * (1 / 138 : ℝ) := by gcongr
  rw [hphi_split]
  have hterm2 :
      ‖(Complex.log (1 + u) - Complex.log (1 + (u0 : ℂ))) / (aLog : ℂ)‖ ≤
        ((10 / 7 : ℝ) * (1 / 138 : ℝ)) / (2 / 5 : ℝ) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg aLog_pos.le]
    exact div_le_div₀ (by positivity) hlog_diff (by positivity) aLog_bounds.1.le
  calc
    ‖((sig0 - Real.log (1 + u0) / aLog - 9 / 4 : ℝ) : ℂ) -
        (Complex.log (1 + u) - Complex.log (1 + (u0 : ℂ))) / (aLog : ℂ)‖
        ≤ ‖((sig0 - Real.log (1 + u0) / aLog - 9 / 4 : ℝ) : ℂ)‖ +
          ‖(Complex.log (1 + u) - Complex.log (1 + (u0 : ℂ))) / (aLog : ℂ)‖ := norm_sub_le _ _
    _ ≤ (3 / 40 : ℝ) + ((10 / 7 : ℝ) * (1 / 138 : ℝ)) / (2 / 5 : ℝ) := by
      have hterm1 : ‖((sig0 - Real.log (1 + u0) / aLog - 9 / 4 : ℝ) : ℂ)‖ ≤ 3 / 40 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hreal_bound
      exact add_le_add hterm1 hterm2
    _ ≤ 13 / 98 := by norm_num

/-- `TentMultiplier.numerator` has infinitely many zeros with `2 < Re(s) < 4`
and arbitrarily large imaginary part (`R < Im(s)`). -/
theorem tent_numerator_infinitely_many_off_axis_zeros (R : ℝ) :
    ∃ s : ℂ, TentMultiplier.numerator s = 0 ∧ 2 < s.re ∧ s.re < 4 ∧ R < s.im := by
  let k0 : ℕ := Nat.succ (Nat.ceil (max 0 ((R + 1) / tPer)))
  obtain ⟨k, hk_ge, hφ⟩ := exists_good_multiple k0
  let c : ℂ := ((9 / 4 : ℝ) : ℂ) + ((k : ℝ) * tPer : ℂ) * I
  let S : Set ℂ := closedBall c (1 / 2)
  have hS_hw : ∀ w ∈ S, (7 / 4 : ℝ) ≤ w.re := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hw)).1
    have hcre : c.re = 9 / 4 := by
      dsimp [c]
      simp [Complex.mul_re]
    rw [Complex.sub_re, hcre] at hre
    linarith
  let K : NNReal := ⟨36 / 49, by norm_num⟩
  have hK_lt : K < 1 := by
    change (36 / 49 : ℝ) < 1
    norm_num
  have hLipOn : LipschitzOnWith K (phiMap k) S := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    · intro w hw
      exact (phiMap_hasDerivAt (hS_hw w hw)).differentiableAt
    · intro w hw
      exact (phiMap_norm_deriv_le (hS_hw w hw) : ‖deriv (phiMap k) w‖ ≤ (K : ℝ))
    · exact convex_closedBall c (1 / 2)
  have hmaps : Set.MapsTo (phiMap k) S S := by
    intro w hw
    have hdist_w : dist w c ≤ 1 / 2 := mem_closedBall.mp hw
    have hc_mem : c ∈ S := mem_closedBall_self (by norm_num)
    have hlip := hLipOn.dist_le_mul w hw c hc_mem
    have hdist_c : dist (phiMap k c) c ≤ 13 / 98 := by
      rw [Complex.dist_eq]
      exact phiMap_center_dist_le k hφ
    rw [mem_closedBall]
    calc
      dist (phiMap k w) c ≤ dist (phiMap k w) (phiMap k c) + dist (phiMap k c) c :=
        dist_triangle _ _ _
      _ ≤ (K : ℝ) * dist w c + (13 / 98 : ℝ) := add_le_add hlip hdist_c
      _ ≤ (36 / 49 : ℝ) * (1 / 2 : ℝ) + (13 / 98 : ℝ) := by
        change (36 / 49 : ℝ) * dist w c + 13 / 98 ≤ _
        linarith
      _ = 1 / 2 := by norm_num
  have hcontract : ContractingWith K (hmaps.restrict (phiMap k) S S) :=
    ⟨hK_lt, hLipOn.mapsToRestrict hmaps⟩
  have hc_mem : c ∈ S := mem_closedBall_self (by norm_num)
  obtain ⟨w, hw_mem, hfix, _⟩ :=
    hcontract.exists_fixedPoint' (isClosed_closedBall.isComplete) hmaps hc_mem (edist_ne_top c _)
  -- Convert fixed point `phiMap k w = w` into `TentMultiplier.numerator (w + 1) = 0`.
  have hfix' : phiMap k w = w := hfix
  have hexp_eq : Complex.exp (-w * (aLog : ℂ)) =
      (1 / 2 : ℂ) * (1 + Complex.exp (-w * (bLog : ℂ))) := by
    have hlin : -w * (aLog : ℂ) = -(bLog : ℂ) +
        ((-(k : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) +
        Complex.log (1 + Complex.exp (-w * (bLog : ℂ))) := by
      have ha_ne : (aLog : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr aLog_pos.ne'
      have hkt : tPer * aLog = 2 * Real.pi := by
        unfold tPer
        field_simp [aLog_pos.ne']
      have hw_mul : w * (aLog : ℂ) =
          (phiMap k w) * (aLog : ℂ) := congrArg (· * (aLog : ℂ)) hfix'.symm
      dsimp [phiMap] at hw_mul
      have hsig : (sig0 : ℂ) * (aLog : ℂ) = (bLog : ℂ) := by
        unfold sig0
        exact_mod_cast (div_mul_cancel₀ bLog aLog_pos.ne')
      rw [sub_mul, add_mul, mul_right_comm, hsig, div_mul_cancel₀ _ ha_ne] at hw_mul
      have hkt_c : ((k : ℂ) * (tPer : ℂ) * (aLog : ℂ) * I) =
          ((k : ℤ) : ℂ) * (2 * Real.pi * I) := by
        have hkreal : ((k : ℝ) * tPer) * aLog = (k : ℝ) * (2 * Real.pi) := by
          rw [mul_assoc, hkt]
        calc
          ((k : ℂ) * (tPer : ℂ) * (aLog : ℂ) * I)
              = ((((k : ℝ) * tPer) * aLog : ℝ) : ℂ) * I := by push_cast; ring
          _ = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I := by rw [hkreal]
          _ = ((k : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
      have hneg_k : (((-(k : ℤ) : ℤ) : ℂ)) = -((k : ℤ) : ℂ) := by push_cast; rfl
      rw [hkt_c] at hw_mul
      rw [hneg_k]
      linear_combination -hw_mul
    rw [hlin, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_neg,
      show Complex.exp (bLog : ℂ) = (2 : ℂ) by
        rw [← Complex.ofReal_exp, show bLog = Real.log 2 from rfl, Real.exp_log (by norm_num)]
        norm_num]
    have hre_pos : 0 < (1 + Complex.exp (-w * (bLog : ℂ))).re := by
      have hu := exp_neg_mul_bLog_norm_lt (hS_hw w hw_mem)
      have := (abs_le.mp ((Complex.abs_re_le_norm (Complex.exp (-w * (bLog : ℂ)))).trans hu.le)).1
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hne : 1 + Complex.exp (-w * (bLog : ℂ)) ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at hre_pos
      exact lt_irrefl 0 hre_pos
    rw [Complex.exp_log hne, one_div]
  -- Relate `exp (-w * aLog)` and `exp (-w * bLog)` to `(4/3)^w` and `2^w`.
  have h2w : (2 : ℂ) ^ w = (Complex.exp (-w * (bLog : ℂ)))⁻¹ := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
      show Complex.log (2 : ℂ) = (bLog : ℂ) by simp [bLog],
      ← Complex.exp_neg]
    congr 1
    ring
  have h43w : ((4 / 3 : ℝ) : ℂ) ^ w = Complex.exp (w * (bLog : ℂ) - w * (aLog : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : ((4 / 3 : ℝ) : ℂ) ≠ 0)]
    have hlog43 : Complex.log ((4 / 3 : ℝ) : ℂ) = (bLog : ℂ) - (aLog : ℂ) := by
      rw [← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 4 / 3)]
      have : Real.log (4 / 3 : ℝ) = Real.log 2 - Real.log (3 / 2) := by
        rw [← Real.log_div (by norm_num) (by norm_num)]
        norm_num
      exact_mod_cast this
    rw [hlog43]
    congr 1
    ring
  have hnum_zero : TentMultiplier.numerator (w + 1) = 0 := by
    unfold TentMultiplier.numerator
    rw [show w + 1 - 1 = w by ring, h2w, h43w, Complex.exp_sub,
      show Complex.exp (w * (bLog : ℂ)) = (Complex.exp (-w * (bLog : ℂ)))⁻¹ by
        rw [← Complex.exp_neg]; congr 1; ring,
      show (Complex.exp (-w * (bLog : ℂ)))⁻¹ / Complex.exp (w * (aLog : ℂ)) =
        (Complex.exp (-w * (bLog : ℂ)))⁻¹ * Complex.exp (-w * (aLog : ℂ)) by
        rw [div_eq_mul_inv, show (Complex.exp (w * (aLog : ℂ)))⁻¹ = Complex.exp (-w * (aLog : ℂ)) by
          rw [show -w * (aLog : ℂ) = -(w * (aLog : ℂ)) by ring, Complex.exp_neg]],
      hexp_eq]
    have hexp_ne : Complex.exp (-w * (bLog : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hexp_ne]
    ring
  -- Check bounds on `s = w + 1`.
  have hw_dist : ‖w - c‖ ≤ 1 / 2 := by
    simpa [Complex.dist_eq] using mem_closedBall.mp hw_mem
  have hw_re_hi : w.re ≤ 11 / 4 := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hw_dist)).2
    have hcre : c.re = 9 / 4 := by
      dsimp [c]
      simp [Complex.mul_re]
    rw [Complex.sub_re, hcre] at hre
    linarith
  have hw_im_lo : (k : ℝ) * tPer - 1 / 2 ≤ w.im := by
    have him := (abs_le.mp ((Complex.abs_im_le_norm (w - c)).trans hw_dist)).1
    have hcim : c.im = (k : ℝ) * tPer := by
      dsimp [c]
      simp [Complex.mul_im]
    rw [Complex.sub_im, hcim] at him
    linarith
  refine ⟨w + 1, hnum_zero, ?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.one_re]
    linarith [hS_hw w hw_mem]
  · simp only [Complex.add_re, Complex.one_re]
    linarith
  · simp only [Complex.add_im, Complex.one_im, add_zero]
    have hk_real : (R + 1) / tPer < (k : ℝ) := by
      have hceil : max 0 ((R + 1) / tPer) ≤ (k0 : ℝ) - 1 := by
        have : max 0 ((R + 1) / tPer) ≤ (Nat.ceil (max 0 ((R + 1) / tPer)) : ℝ) := Nat.le_ceil _
        push_cast [k0]
        linarith
      have hge : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
      have := le_max_right 0 ((R + 1) / tPer)
      linarith
    have ht_pos : 0 < tPer := div_pos (mul_pos (by norm_num) Real.pi_pos) aLog_pos
    have : R + 1 < (k : ℝ) * tPer := (div_lt_iff₀ ht_pos).mp hk_real
    linarith

end OffAxisZeros

end RhAstraSynthesis
