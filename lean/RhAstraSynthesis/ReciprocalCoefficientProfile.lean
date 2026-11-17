import RhAstraSynthesis.ReciprocalGevreyMajorant
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Complex reciprocal coefficient profiles

The positive-index series converges uniformly on every closed subdisk, with
one radius parameter controlling every Taylor order.
-/

noncomputable section

namespace RhAstraSynthesis

/-- The real normalized derivative is cast only after division by `s!`. -/
def reciprocalProfileTerm (P : ℕ → Polynomial ℝ) (s n : ℕ) (u : ℂ) : ℂ :=
  (((((Polynomial.derivative^[s]) (P (n + 1))).eval 0) /
    (s.factorial : ℝ) : ℝ) : ℂ) * u ^ (n + 1)

/-- Positive-index coefficient profile, with no degree-zero family term. -/
def reciprocalCoefficientProfile (P : ℕ → Polynomial ℝ) (s : ℕ) (u : ℂ) : ℂ :=
  ∑' n, reciprocalProfileTerm P s n u

lemma norm_reciprocalProfileTerm (P : ℕ → Polynomial ℝ) (s n : ℕ) (u : ℂ) :
    ‖reciprocalProfileTerm P s n u‖ =
      |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
        (s.factorial : ℝ) * ‖u‖ ^ (n + 1) := by
  simp only [reciprocalProfileTerm, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ s.factorial by positivity)]

lemma reciprocalProfileTerm_le (P : ℕ → Polynomial ℝ) (s n : ℕ)
    {r : ℝ} {u : ℂ} (hu : ‖u‖ ≤ r) :
    ‖reciprocalProfileTerm P s n u‖ ≤
      |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
        (s.factorial : ℝ) * r ^ (n + 1) := by
  rw [norm_reciprocalProfileTerm]
  gcongr

/-- From a real radial majorant to absolute complex convergence, a norm bound,
and uniform convergence of the actual partial sums on the entire closed disk. -/
theorem reciprocalProfile_of_summable (P : ℕ → Polynomial ℝ) (s : ℕ)
    {r B : ℝ}
    (hs : Summable (fun n : ℕ =>
      |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
        (s.factorial : ℝ) * r ^ (n + 1)))
    (hb : (∑' n : ℕ, |((Polynomial.derivative^[s]) (P (n + 1))).eval 0| /
      (s.factorial : ℝ) * r ^ (n + 1)) ≤ B) :
    (∀ u : ℂ, ‖u‖ ≤ r →
      Summable (fun n => ‖reciprocalProfileTerm P s n u‖) ∧
      Summable (fun n => reciprocalProfileTerm P s n u) ∧
      ‖reciprocalCoefficientProfile P s u‖ ≤ B) ∧
    TendstoUniformlyOn
      (fun N u => ∑ n ∈ Finset.range N, reciprocalProfileTerm P s n u)
      (reciprocalCoefficientProfile P s) Filter.atTop {u : ℂ | ‖u‖ ≤ r} := by
  constructor
  · intro u hu
    have hn : Summable (fun n => ‖reciprocalProfileTerm P s n u‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun n => reciprocalProfileTerm_le P s n hu) hs
    refine ⟨hn, hn.of_norm, ?_⟩
    exact (norm_tsum_le_tsum_norm hn).trans
      ((hn.tsum_le_tsum (fun n => reciprocalProfileTerm_le P s n hu) hs).trans hb)
  · exact tendstoUniformlyOn_tsum_nat hs (fun n u hu => reciprocalProfileTerm_le P s n hu)

/-- The radius parameter is chosen before both the Taylor order and the complex
point. The bound has exactly the same constants as the real radial majorant. -/
theorem polynomial_reciprocal_profiles_all_radii
    (P : ℕ → Polynomial ℝ) {C R : ℝ}
    (hC : 0 < C) (hR : 0 < R)
    (hdegree : ∀ m, 0 < m → (P m).natDegree ≤ m)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m) :
    ∀ r : ℝ, 0 ≤ r → r < R → ∃ L : ℕ, 0 < L ∧
      (r / R) * Real.exp (2 / Real.sqrt (L : ℝ)) < 1 ∧ ∀ s : ℕ,
      (∀ u : ℂ, ‖u‖ ≤ r →
        Summable (fun n => ‖reciprocalProfileTerm P s n u‖) ∧
        Summable (fun n => reciprocalProfileTerm P s n u) ∧
        ‖reciprocalCoefficientProfile P s u‖ ≤
          C / (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) *
            (64 * (L : ℝ) /
              (1 - (r / R) * Real.exp (2 / Real.sqrt (L : ℝ))) ^ 3) ^ s *
            (s.factorial : ℝ)) ∧
      TendstoUniformlyOn
        (fun N u => ∑ n ∈ Finset.range N, reciprocalProfileTerm P s n u)
        (reciprocalCoefficientProfile P s) Filter.atTop {u : ℂ | ‖u‖ ≤ r} := by
  intro r hr hrR
  obtain ⟨L, hL, hσ, hall⟩ := polynomial_reciprocal_family_gevrey_all_radii
    P hC hR hdegree hsample r hr hrR
  exact ⟨L, hL, hσ, fun s => reciprocalProfile_of_summable P s (hall s).1 (hall s).2⟩

/-- Closed-subdisk uniform convergence suffices for holomorphy; no claim is
made about convergence on the boundary of the outer disk. -/
theorem reciprocalCoefficientProfile_differentiableOn_of_uniform
    (P : ℕ → Polynomial ℝ) (s : ℕ) {R : ℝ}
    (huniform : ∀ r : ℝ, 0 ≤ r → r < R →
      TendstoUniformlyOn
        (fun N u => ∑ n ∈ Finset.range N, reciprocalProfileTerm P s n u)
        (reciprocalCoefficientProfile P s) Filter.atTop {u : ℂ | ‖u‖ ≤ r}) :
    DifferentiableOn ℂ (reciprocalCoefficientProfile P s) {u : ℂ | ‖u‖ < R} := by
  have hlocal : TendstoLocallyUniformlyOn
      (fun N u => ∑ n ∈ Finset.range N, reciprocalProfileTerm P s n u)
      (reciprocalCoefficientProfile P s) Filter.atTop {u : ℂ | ‖u‖ < R} := by
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro u hu
    obtain ⟨r, hur, hrR⟩ := exists_between hu
    refine ⟨{v : ℂ | ‖v‖ ≤ r}, ?_, huniform r ((norm_nonneg u).trans hur.le) hrR⟩
    apply nhdsWithin_le_nhds
    exact Filter.mem_of_superset
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hur)
      (fun v hv => hv.le)
  apply hlocal.differentiableOn
    (Filter.Eventually.of_forall fun N => ?_) (isOpen_lt continuous_norm continuous_const)
  exact DifferentiableOn.fun_sum fun n _ =>
    (show Differentiable ℂ (reciprocalProfileTerm P s n) from
      (differentiable_id.pow (n + 1)).const_mul _).differentiableOn

/-- Every Taylor-order profile is holomorphic throughout the open radius-`R`
disk under the same reciprocal sample hypotheses as the radial majorant. -/
theorem polynomial_reciprocal_profiles_holomorphic
    (P : ℕ → Polynomial ℝ) {C R : ℝ}
    (hC : 0 < C) (hR : 0 < R)
    (hdegree : ∀ m, 0 < m → (P m).natDegree ≤ m)
    (hsample : ∀ m, 0 < m → ∀ k : ℕ, 0 < k →
      |(P m).eval (1 / (k : ℝ))| ≤ C * (1 / R) ^ m) :
    ∀ s : ℕ, DifferentiableOn ℂ (reciprocalCoefficientProfile P s)
      {u : ℂ | ‖u‖ < R} := by
  intro s
  apply reciprocalCoefficientProfile_differentiableOn_of_uniform
  intro r hr hrR
  obtain ⟨L, hL, hσ, hall⟩ :=
    polynomial_reciprocal_profiles_all_radii P hC hR hdegree hsample r hr hrR
  exact (hall s).2

@[simp] theorem reciprocalCoefficientProfile_zero (P : ℕ → Polynomial ℝ) (s : ℕ) :
    reciprocalCoefficientProfile P s 0 = 0 := by
  simp [reciprocalCoefficientProfile, reciprocalProfileTerm]

end RhAstraSynthesis
