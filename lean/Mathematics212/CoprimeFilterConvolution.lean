import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathematics212.CoprimeMobiusFinite
import Mathematics212.DivisorMomentBridge

/-!
# Local coprime filter weights, density bounds, and fractional-moment split envelopes

Formalizes the structural arithmetic and analytic-split inequalities:
1. `local_filter_complement` & `local_filter_bounds`: for `p > 0`, `1 - 1/(p+1) = p/(p+1)`
   and both local prime weights `1/(p+1)` and `p/(p+1)` lie in `(0, 1)`.
2. `coprime_density_r_pos` & `coprime_density_r_le_one`: the modulus factor
   `r(d) = ∏_{p ∣ d} (p / (p + 1))` in `CoprimeMobiusFinite` satisfies `0 < r(d) ≤ 1` for all `d : ℕ`.
3. `quadratic_split_envelope` & `weighted_quadratic_split_envelope`:
   `(a + b)^2 ≤ 2 a^2 + 2 b^2` for splitting low-scale (`k ≤ √v`) and high-scale (`k > √v`) sums.
4. `high_scale_three_fourths_weight_bound`: for `0 < u ≤ r` (with `u = v^(1/8)` and `r = k^(1/4)`),
   `1 / r^4 ≤ (1 / u) * (1 / r^3)`, corresponding to `k^(-1) ≤ v^(-1/8) * k^(-3/4)`.
5. `uniform_modulus_error_envelope`: transfers `A(d) ≤ A(1) * τ(d)` into the squared
   modulus-uniform error bound `(f(d)/d)^2 * A(d)^2 * Y ≤ (f(d)/d)^2 * A(1)^2 * τ(d)^2 * Y`.
-/

namespace Mathematics212

/-- Local prime weight complement `1 - 1 / (p + 1) = p / (p + 1)` for `p ≥ 0`. -/
theorem local_filter_complement (p : ℝ) (hp : 0 ≤ p) :
    1 - 1 / (p + 1) = p / (p + 1) := by
  have hp1 : p + 1 ≠ 0 := by linarith
  field_simp [hp1]
  ring

/-- Strict unit-interval bounds for the local prime weights `p / (p + 1)` and `1 / (p + 1)`. -/
theorem local_filter_bounds (p : ℝ) (hp : 0 < p) :
    0 < p / (p + 1) ∧ p / (p + 1) < 1 ∧ 0 < 1 / (p + 1) ∧ 1 / (p + 1) < 1 := by
  have hp1 : 0 < p + 1 := by linarith
  refine ⟨div_pos hp hp1, (div_lt_one hp1).2 (by linarith),
    one_div_pos.mpr hp1, (div_lt_one hp1).2 (by linarith)⟩

private theorem finset_prod_le_one_of_nonneg {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    ∏ i ∈ s, g i ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have ha0 : 0 ≤ g a := hg0 a (Finset.mem_insert_self a s)
      have ha1 : g a ≤ 1 := hg1 a (Finset.mem_insert_self a s)
      have hs0 : 0 ≤ ∏ i ∈ s, g i :=
        Finset.prod_nonneg (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
      have hs1 : ∏ i ∈ s, g i ≤ 1 :=
        ih (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
           (fun i hi => hg1 i (Finset.mem_insert_of_mem hi))
      calc
        g a * ∏ i ∈ s, g i ≤ 1 * ∏ i ∈ s, g i := mul_le_mul_of_nonneg_right ha1 hs0
        _ ≤ 1 := by linarith

/-- The modulus-dependent coprime factor `r(d) = ∏_{p ∣ d} (p / (p + 1))` is strictly positive. -/
theorem coprime_density_r_pos (d : ℕ) :
    0 < CoprimeMobius.r d := by
  unfold CoprimeMobius.r
  apply Finset.prod_pos
  intro p hp
  have hp_pos : 0 < p := Nat.pos_of_mem_primeFactors hp
  positivity

/-- The modulus-dependent coprime factor `r(d)` is bounded above by `1` for all `d : ℕ`. -/
theorem coprime_density_r_le_one (d : ℕ) :
    CoprimeMobius.r d ≤ 1 := by
  unfold CoprimeMobius.r
  apply finset_prod_le_one_of_nonneg
  · intro p _
    positivity
  · intro p _
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    exact (div_le_one hp1).2 (by linarith)

/-- Combined uniform bounds `0 < r(d) ≤ 1` used in `modulus-uniform-fractional-moment.md` §3. -/
theorem coprime_density_r_bounds (d : ℕ) :
    0 < CoprimeMobius.r d ∧ CoprimeMobius.r d ≤ 1 :=
  ⟨coprime_density_r_pos d, coprime_density_r_le_one d⟩

/-- Quadratic split envelope `(a + b)^2 ≤ 2 a^2 + 2 b^2` separating low and high divisor scales. -/
theorem quadratic_split_envelope (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Weighted quadratic split envelope `w * (a + b)^2 ≤ 2 * w * a^2 + 2 * w * b^2` for `w ≥ 0`. -/
theorem weighted_quadratic_split_envelope {w a b : ℝ} (hw : 0 ≤ w) :
    w * (a + b) ^ 2 ≤ 2 * w * a ^ 2 + 2 * w * b ^ 2 := by
  have h := quadratic_split_envelope a b
  calc
    w * (a + b) ^ 2 ≤ w * (2 * a ^ 2 + 2 * b ^ 2) := mul_le_mul_of_nonneg_left h hw
    _ = 2 * w * a ^ 2 + 2 * w * b ^ 2 := by ring

/-- High-scale `s = 3/4` weight reduction (`modulus-uniform-fractional-moment.md` §3, eq. 4):
writing `u = v^(1/8) > 0` and `r = k^(1/4) ≥ u`, we have `1 / r^4 ≤ (1 / u) * (1 / r^3)`. -/
theorem high_scale_three_fourths_weight_bound {u r : ℝ} (hu : 0 < u) (hur : u ≤ r) :
    1 / r ^ 4 ≤ (1 / u) * (1 / r ^ 3) := by
  have hr : 0 < r := lt_of_lt_of_le hu hur
  have hr3 : 0 < r ^ 3 := by positivity
  have hinv_r3 : 0 ≤ 1 / r ^ 3 := div_nonneg zero_le_one hr3.le
  have hinv_u : 1 / r ≤ 1 / u := one_div_le_one_div_of_le hu hur
  calc
    1 / r ^ 4 = (1 / r) * (1 / r ^ 3) := by ring
    _ ≤ (1 / u) * (1 / r ^ 3) := mul_le_mul_of_nonneg_right hinv_u hinv_r3

/-- Transfers `A(d) ≤ A(1) * τ(d)` into the modulus-uniform squared error bound of §4. -/
theorem uniform_modulus_error_envelope {A1 tau_d fd_div_d Y Ad : ℝ}
    (hY : 0 ≤ Y) (hAd_nn : 0 ≤ Ad) (hAd : Ad ≤ A1 * tau_d) :
    fd_div_d ^ 2 * Ad ^ 2 * Y ≤ fd_div_d ^ 2 * A1 ^ 2 * tau_d ^ 2 * Y := by
  have hsq : Ad ^ 2 ≤ (A1 * tau_d) ^ 2 :=
    pow_le_pow_left₀ hAd_nn hAd 2
  have hcoeff : 0 ≤ fd_div_d ^ 2 * Y := by positivity
  calc
    fd_div_d ^ 2 * Ad ^ 2 * Y = (fd_div_d ^ 2 * Y) * Ad ^ 2 := by ring
    _ ≤ (fd_div_d ^ 2 * Y) * (A1 * tau_d) ^ 2 := mul_le_mul_of_nonneg_left hsq hcoeff
    _ = fd_div_d ^ 2 * A1 ^ 2 * tau_d ^ 2 * Y := by ring

end Mathematics212
