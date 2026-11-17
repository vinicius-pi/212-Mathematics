import RhAstraSynthesis.MarkovChebyshevGeneral
import RhAstraSynthesis.MarkovInterior
import RhAstraSynthesis.ChebyshevExponentialEnvelope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Full Measurable Equioscillation Remez Inequality

Formalizes the classical measurable Remez inequality on arbitrary compact intervals
`[a, b]` (`a < b`) and its exponential / Markov–interior corollaries:

* `remez_inequality`: if `P : Polynomial ℝ` satisfies `P.natDegree ≤ n`, `0 ≤ B`,
  `E ⊆ Set.Icc a b` is measurable with `0 < volume.real E`, and `∀ t ∈ E, |P.eval t| ≤ B`,
  then for every `x ∈ Set.Icc a b`,
  `|P.eval x| ≤ (Polynomial.Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B`.
* `remez_exponential_inequality`: if `(b - a) / (1 + 1 / L) ≤ volume.real E` (`L > 0`),
  then `|P.eval x| ≤ Real.exp (2 * (n : ℝ) / Real.sqrt L) * B` for all `x ∈ [a, b]`.
* `remez_markov_interior_derivative_bound`: combines `remez_inequality` with
  `markov_iterate_derivative_interior_le` to control all `s`-th derivatives on `[a, b]`
  from bounds on an arbitrary measurable subset `E ⊆ [a, b]`.

The proof follows Bojanov's elementary Lagrange–Chebyshev construction:
passing from `E` to the compact sublevel `K = {t ∈ [a, b] | |P(t)| ≤ B}`,
extracting `n + 1` nodes `x_k ∈ K` whose sublevel measures match the Chebyshev
nodes `(1 - cos (k π / n)) / 2 * μ(K)`, comparing Lagrange ratios at the right
endpoint via `1`-Lipschitzness of `x ↦ μ(K ∩ [a, x])`, and reducing interior
points `x ∈ [a, b]` to right endpoints via left/right measure splitting.
-/

namespace RhAstraSynthesis

open Polynomial Real MeasureTheory Set

section MeasurePreimageLevel

private lemma volume_real_Ioc_le_sub (x y : ℝ) (hxy : x ≤ y) :
    volume.real (Set.Ioc x y) = y - x := by
  rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)]

private lemma volume_real_Icc_inter_mono {a b x y : ℝ} (K : Set ℝ)
    (hKsub : K ⊆ Set.Icc a b) (hxy : x ≤ y) :
    volume.real (K ∩ Set.Icc a x) ≤ volume.real (K ∩ Set.Icc a y) := by
  refine measureReal_mono (fun t ⟨htK, hta, htx⟩ => ⟨htK, hta, htx.trans hxy⟩) ?_
  have hsub : K ∩ Set.Icc a y ⊆ Set.Icc a b := Set.inter_subset_left.trans hKsub
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) (by simp))

private lemma volume_real_Icc_inter_lip {a b : ℝ} {K : Set ℝ}
    (hKm : MeasurableSet K) (hKsub : K ⊆ Set.Icc a b) {x y : ℝ} (hxy : x ≤ y) :
    volume.real (K ∩ Set.Icc a y) - volume.real (K ∩ Set.Icc a x) ≤ y - x := by
  have hsub : K ∩ Set.Icc a x ⊆ K ∩ Set.Icc a y :=
    fun t ⟨htK, hta, htx⟩ => ⟨htK, hta, htx.trans hxy⟩
  have hfin : volume (K ∩ Set.Icc a y) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono (Set.inter_subset_left.trans hKsub)) (by simp))
  have hsdiff := measureReal_sdiff (μ := volume) hsub (hKm.inter measurableSet_Icc) hfin
  have hsubset : (K ∩ Set.Icc a y) \ (K ∩ Set.Icc a x) ⊆ Set.Ioc x y := by
    rintro t ⟨⟨htK, hta, hty⟩, hnot⟩
    refine ⟨lt_of_not_ge fun hle => hnot ⟨htK, hta, hle⟩, hty⟩
  have hmono : volume.real ((K ∩ Set.Icc a y) \ (K ∩ Set.Icc a x)) ≤ volume.real (Set.Ioc x y) :=
    measureReal_mono hsubset (by simp)
  rw [hsdiff, volume_real_Ioc_le_sub x y hxy] at hmono
  exact hmono

private lemma continuous_volume_real_Icc_inter (a : ℝ) {b : ℝ} {K : Set ℝ}
    (hKm : MeasurableSet K) (hKsub : K ⊆ Set.Icc a b) :
    Continuous (fun x : ℝ => volume.real (K ∩ Set.Icc a x)) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε, hε, fun t ht => ?_⟩
  rw [Real.dist_eq] at ht ⊢
  rcases le_total t x with htx | hxt
  · have h0 : 0 ≤ volume.real (K ∩ Set.Icc a x) - volume.real (K ∩ Set.Icc a t) :=
      sub_nonneg.mpr (volume_real_Icc_inter_mono K hKsub htx)
    have h1 := volume_real_Icc_inter_lip hKm hKsub htx
    have hxt_lt : x - t < ε := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htx)] at ht
      exact ht
    rw [abs_sub_comm, abs_of_nonneg h0]
    linarith
  · have h0 : 0 ≤ volume.real (K ∩ Set.Icc a t) - volume.real (K ∩ Set.Icc a x) :=
      sub_nonneg.mpr (volume_real_Icc_inter_mono K hKsub hxt)
    have h1 := volume_real_Icc_inter_lip hKm hKsub hxt
    have htx_lt : t - x < ε := by
      rw [abs_of_nonneg (sub_nonneg.mpr hxt)] at ht
      exact ht
    rw [abs_of_nonneg h0]
    linarith

private lemma exists_mem_compact_measure_eq {a b e y : ℝ} (_hab : a ≤ b) {K : Set ℝ}
    (hK : IsCompact K) (hKsub : K ⊆ Set.Icc a b) (he : volume.real K = e)
    (he_pos : 0 < e) (hy0 : 0 ≤ y) (hye : y ≤ e) :
    ∃ x ∈ K, volume.real (K ∩ Set.Icc a x) = y := by
  let φ : ℝ → ℝ := fun x => volume.real (K ∩ Set.Icc a x)
  have hKm : MeasurableSet K := hK.measurableSet
  have hφ_cont : Continuous φ := continuous_volume_real_Icc_inter a hKm hKsub
  have hK_ne : K.Nonempty := by
    by_contra hEmp
    rw [Set.not_nonempty_iff_eq_empty] at hEmp
    simp [hEmp] at he
    linarith
  let A : Set ℝ := {x ∈ K | φ x ≤ y}
  have hA_closed : IsClosed A := hK.isClosed.inter (isClosed_Iic.preimage hφ_cont)
  have hA_compact : IsCompact A := hK.of_isClosed_subset hA_closed (fun _ hx => hx.1)
  let xmin : ℝ := sInf K
  have hxmin_mem : xmin ∈ K := hK.isClosed.csInf_mem hK_ne hK.bddBelow
  have hxmin_sub : K ∩ Set.Icc a xmin ⊆ ({xmin} : Set ℝ) := by
    intro z ⟨hzK, _, hzle⟩
    have hge : xmin ≤ z := csInf_le hK.bddBelow hzK
    simp [le_antisymm hzle hge]
  have hφ_xmin : φ xmin ≤ 0 := by
    dsimp [φ]
    have h0 := measureReal_mono hxmin_sub (by simp : volume ({xmin} : Set ℝ) ≠ ⊤)
    simp only [Measure.real, Real.volume_singleton, ENNReal.toReal_zero] at h0
    exact h0
  have hA_ne : A.Nonempty := ⟨xmin, hxmin_mem, le_trans hφ_xmin hy0⟩
  let xstar : ℝ := sSup A
  have hxstar_mem : xstar ∈ A := hA_closed.csSup_mem hA_ne hA_compact.bddAbove
  have hxstar_K : xstar ∈ K := hxstar_mem.1
  have hxstar_Icc : xstar ∈ Set.Icc a b := hKsub hxstar_K
  have hφ_le : φ xstar ≤ y := hxstar_mem.2
  refine ⟨xstar, hxstar_K, ?_⟩
  rcases eq_or_lt_of_le hye with heq_y | hylt
  · let xmax : ℝ := sSup K
    have hxmax_mem : xmax ∈ K := hK.isClosed.csSup_mem hK_ne hK.bddAbove
    have hK_sub_xmax : K ⊆ Set.Icc a xmax :=
      fun z hz => ⟨(hKsub hz).1, le_csSup hK.bddAbove hz⟩
    have hφ_xmax : φ xmax = e := by
      dsimp [φ]
      rw [Set.inter_eq_left.mpr hK_sub_xmax, he]
    have hxmax_A : xmax ∈ A := ⟨hxmax_mem, le_of_eq (hφ_xmax.trans heq_y.symm)⟩
    have hxmax_le : xmax ≤ xstar := le_csSup hA_compact.bddAbove hxmax_A
    have hxstar_le : xstar ≤ xmax := le_csSup hK.bddAbove hxstar_K
    have heq : xstar = xmax := le_antisymm hxstar_le hxmax_le
    rw [heq]
    exact hφ_xmax.trans heq_y.symm
  · by_contra hne
    have hφ_lt : φ xstar < y := lt_of_le_of_ne hφ_le hne
    have hε : 0 < y - φ xstar := sub_pos.mpr hφ_lt
    obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.continuous_iff.mp hφ_cont) xstar (y - φ xstar) hε
    have h_near : ∀ z : ℝ, |z - xstar| < δ → φ z < y := by
      intro z hz
      have hdz := hδ (a := z) (by simpa [Real.dist_eq] using hz)
      rw [Real.dist_eq] at hdz
      linarith [(abs_lt.mp hdz).2]
    have hpartition : K = (K ∩ Set.Icc a xstar) ∪ (K ∩ Set.Ioc xstar b) := by
      have hIcc : Set.Icc a b = Set.Icc a xstar ∪ Set.Ioc xstar b :=
        (Set.Icc_union_Ioc_eq_Icc hxstar_Icc.1 hxstar_Icc.2).symm
      have hK_eq : K = K ∩ Set.Icc a b := (Set.inter_eq_left.mpr hKsub).symm
      conv_lhs => rw [hK_eq, hIcc, Set.inter_union_distrib_left]
    have hdisj : Disjoint (K ∩ Set.Icc a xstar) (K ∩ Set.Ioc xstar b) :=
      Set.disjoint_left.mpr fun z hz1 hz2 => by linarith [hz1.2.2, hz2.2.1]
    have hfin_right : volume (K ∩ Set.Ioc xstar b) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp))
    have hfin_left : volume (K ∩ Set.Icc a xstar) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp))
    have hsum : e = φ xstar + volume.real (K ∩ Set.Ioc xstar b) := by
      calc
        e = volume.real K := he.symm
        _ = volume.real ((K ∩ Set.Icc a xstar) ∪ (K ∩ Set.Ioc xstar b)) := by rw [← hpartition]
        _ = φ xstar + volume.real (K ∩ Set.Ioc xstar b) :=
          measureReal_union hdisj (hKm.inter measurableSet_Ioc) hfin_left hfin_right
    have hright_pos : 0 < volume.real (K ∩ Set.Ioc xstar b) := by linarith
    by_cases hhit : ∃ z ∈ K, xstar < z ∧ z < xstar + δ
    · obtain ⟨z, hzK, hzx1, hzx2⟩ := hhit
      have hz_abs : |z - xstar| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
      have hzA : z ∈ A := ⟨hzK, le_of_lt (h_near z hz_abs)⟩
      have hz_le : z ≤ xstar := le_csSup hA_compact.bddAbove hzA
      linarith
    · push Not at hhit
      let R : Set ℝ := K ∩ Set.Icc (xstar + δ) b
      have hReq : K ∩ Set.Ioc xstar b = R := by
        ext z
        refine ⟨fun ⟨hzK, hz1, hz2⟩ => ⟨hzK, hhit z hzK hz1, hz2⟩,
          fun ⟨hzK, hz1, hz2⟩ => ⟨hzK, by linarith, hz2⟩⟩
      have hR_pos : 0 < volume.real R := hReq ▸ hright_pos
      have hR_ne : R.Nonempty := by
        by_contra hEmp
        rw [Set.not_nonempty_iff_eq_empty] at hEmp
        simp [hEmp] at hR_pos
      have hR_compact : IsCompact R := hK.inter_right isClosed_Icc
      let u : ℝ := sInf R
      have hu_mem : u ∈ R := hR_compact.isClosed.csInf_mem hR_ne hR_compact.bddBelow
      have huK : u ∈ K := hu_mem.1
      have hu_ge : xstar + δ ≤ u := hu_mem.2.1
      have hu_gt : xstar < u := by linarith
      have hu_sub : K ∩ Set.Icc a u ⊆ (K ∩ Set.Icc a xstar) ∪ ({u} : Set ℝ) := by
        intro w ⟨hwK, hwa, hwu⟩
        rcases eq_or_lt_of_le hwu with rfl | hwlt
        · exact Or.inr rfl
        · left
          refine ⟨hwK, hwa, ?_⟩
          by_contra hnot
          have hwx : xstar < w := lt_of_not_ge hnot
          have hw_ge : xstar + δ ≤ w := hhit w hwK hwx
          have hw_le_b : w ≤ b := le_trans hwlt.le (hKsub huK).2
          have hwR : w ∈ R := ⟨hwK, hw_ge, hw_le_b⟩
          have hu_le_w : u ≤ w := csInf_le hR_compact.bddBelow hwR
          linarith
      have hfin_u : volume (K ∩ Set.Icc a xstar ∪ ({u} : Set ℝ)) ≠ ⊤ := by
        refine ne_of_lt (lt_of_le_of_lt (measure_union_le _ _) (ENNReal.add_lt_top.mpr ⟨?_, by simp⟩))
        exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp)
      have hφ_u : φ u ≤ φ xstar := by
        dsimp [φ]
        calc
          volume.real (K ∩ Set.Icc a u)
              ≤ volume.real ((K ∩ Set.Icc a xstar) ∪ ({u} : Set ℝ)) :=
            measureReal_mono hu_sub hfin_u
          _ ≤ volume.real (K ∩ Set.Icc a xstar) + volume.real ({u} : Set ℝ) :=
            measureReal_union_le _ _
          _ = volume.real (K ∩ Set.Icc a xstar) := by
            simp [Measure.real]
      have huA : u ∈ A := ⟨huK, le_of_lt (lt_of_le_of_lt hφ_u hφ_lt)⟩
      have hu_le : u ≤ xstar := le_csSup hA_compact.bddAbove huA
      linarith

end MeasurePreimageLevel

section ChebyshevLagrangeNodes

private noncomputable def chebNodeAsc (n k : ℕ) : ℝ :=
  Chebyshev.node n (n - k)

private lemma chebNodeAsc_mem_Icc (n k : ℕ) :
    chebNodeAsc n k ∈ Set.Icc (-1 : ℝ) 1 :=
  Chebyshev.node_mem_Icc

private lemma chebNodeAsc_strictMonoOn (n : ℕ) :
    StrictMonoOn (chebNodeAsc n) (Finset.range (n + 1)) := by
  intro i hi j hj hij
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_coe.mp hi |> Finset.mem_range.mp)
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_coe.mp hj |> Finset.mem_range.mp)
  have hsub : n - j < n - i := by omega
  have hni_mem : n - i ∈ (Finset.range (n + 1) : Set ℕ) :=
    Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
  have hnj_mem : n - j ∈ (Finset.range (n + 1) : Set ℕ) :=
    Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
  exact Chebyshev.strictAntiOn_node n hnj_mem hni_mem hsub

private lemma eval_T_chebNodeAsc {n k : ℕ} (_hk : k ≤ n) :
    (Chebyshev.T ℝ n).eval (chebNodeAsc n k) = (-1 : ℝ) ^ (n - k) := by
  unfold chebNodeAsc
  exact Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (Nat.sub_le n k))

private lemma chebNodeAsc_sign_prod {n k : ℕ} (hk : k ≤ n) :
    0 < (-1 : ℝ) ^ (n - k) *
      ∏ i ∈ (Finset.range (n + 1)).erase k, (chebNodeAsc n k - chebNodeAsc n i) := by
  have hmono := chebNodeAsc_strictMonoOn n
  have hk_mem : k ∈ (Finset.range (n + 1) : Set ℕ) :=
    Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hleft : 0 < ∏ i ∈ Finset.range k, (chebNodeAsc n k - chebNodeAsc n i) := by
    refine Finset.prod_pos fun i hi => sub_pos.mpr ?_
    have hi_lt : i < k := Finset.mem_range.mp hi
    have hi_mem : i ∈ (Finset.range (n + 1) : Set ℕ) :=
      Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    exact hmono hi_mem hk_mem hi_lt
  have hright : 0 < ∏ i ∈ Finset.Ioc k n, ((-1 : ℝ) * (chebNodeAsc n k - chebNodeAsc n i)) := by
    refine Finset.prod_pos fun i hi => mul_pos_of_neg_of_neg (by norm_num) (sub_neg.mpr ?_)
    have hi_pair := Finset.mem_Ioc.mp hi
    have hi_mem : i ∈ (Finset.range (n + 1) : Set ℕ) :=
      Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    exact hmono hk_mem hi_mem hi_pair.1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ioc] at hright
  have hunion : (Finset.range (n + 1)).erase k = Finset.range k ∪ Finset.Ioc k n := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.range k) (Finset.Ioc k n) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb _
    have := Finset.mem_range.mp ha
    have := Finset.mem_Ioc.mp hb
    omega
  rw [hunion, Finset.prod_union hdisj]
  calc
    0 < (∏ i ∈ Finset.range k, (chebNodeAsc n k - chebNodeAsc n i)) *
          ((-1 : ℝ) ^ (n - k) * ∏ i ∈ Finset.Ioc k n, (chebNodeAsc n k - chebNodeAsc n i)) :=
      mul_pos hleft hright
    _ = (-1 : ℝ) ^ (n - k) *
          ((∏ i ∈ Finset.range k, (chebNodeAsc n k - chebNodeAsc n i)) *
            ∏ i ∈ Finset.Ioc k n, (chebNodeAsc n k - chebNodeAsc n i)) := by ring

private lemma chebNodeAsc_lagrange_abs_sum (n : ℕ) {Y : ℝ} (_hY : 1 ≤ Y) :
    ∑ k ∈ Finset.range (n + 1),
        ∏ i ∈ (Finset.range (n + 1)).erase k,
          ((Y - chebNodeAsc n i) / |chebNodeAsc n k - chebNodeAsc n i|) =
      (Chebyshev.T ℝ n).eval Y := by
  let t : ℕ → ℝ := chebNodeAsc n
  let S : Finset ℕ := Finset.range (n + 1)
  have hTdeg : (Chebyshev.T ℝ n).degree < S.card := by
    rw [Finset.card_range, Chebyshev.degree_T ℝ n]
    exact_mod_cast Nat.lt_succ_self n
  have hT_interp :
      Chebyshev.T ℝ n =
        Lagrange.interpolate S t (fun k => (Chebyshev.T ℝ n).eval (t k)) :=
    Lagrange.eq_interpolate (chebNodeAsc_strictMonoOn n).injOn hTdeg
  have hterm : ∀ k ∈ S,
      (∏ i ∈ S.erase k, ((Y - t i) / |t k - t i|)) =
        (Chebyshev.T ℝ n).eval (t k) * (Lagrange.basis S t k).eval Y := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsign := chebNodeAsc_sign_prod hk_le
    have hprod_ne : ∏ i ∈ S.erase k, (t k - t i) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hsign
      exact lt_irrefl 0 hsign
    have hprod_div :
        (∏ i ∈ S.erase k, ((Y - t i) / |t k - t i|)) =
          (∏ i ∈ S.erase k, (Y - t i)) / (∏ i ∈ S.erase k, |t k - t i|) := by
      rw [Finset.prod_div_distrib]
    have hbasis_eval :
        (Lagrange.basis S t k).eval Y =
          (∏ i ∈ S.erase k, (Y - t i)) / (∏ i ∈ S.erase k, (t k - t i)) := by
      unfold Lagrange.basis Lagrange.basisDivisor
      rw [eval_prod]
      have hdiv : ∀ i ∈ S.erase k,
          (C (t k - t i)⁻¹ * (X - C (t i))).eval Y = (Y - t i) / (t k - t i) := by
        intro i _
        simp [div_eq_inv_mul, mul_comm]
      rw [Finset.prod_congr rfl hdiv, Finset.prod_div_distrib]
    have habs_val : ∏ i ∈ S.erase k, |t k - t i| =
        (-1 : ℝ) ^ (n - k) * ∏ i ∈ S.erase k, (t k - t i) := by
      rw [← Finset.abs_prod, ← abs_of_pos hsign, abs_mul, abs_neg_one_pow, one_mul]
    rw [hprod_div, habs_val, eval_T_chebNodeAsc hk_le, hbasis_eval]
    have hsgn2 : ((-1 : ℝ) ^ (n - k)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    field_simp [hprod_ne]
    rw [hsgn2, mul_one]
  rw [Finset.sum_congr rfl hterm]
  conv_rhs => rw [hT_interp, Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [eval_mul, eval_C]

end ChebyshevLagrangeNodes

section RemezCore

private lemma prod_le_prod_nonneg {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))

private lemma remez_right_endpoint_of_compact {n : ℕ} (_hn : 1 ≤ n) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Set.Icc a b)
    (he_pos : 0 < volume.real K) (hKbnd : ∀ t ∈ K, |P.eval t| ≤ B) :
    |P.eval b| ≤ B * (Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real K - 1) := by
  let e : ℝ := volume.real K
  have he_le : e ≤ b - a := by
    have hm := measureReal_mono hKsub (by simp : volume (Set.Icc a b) ≠ ⊤)
    rwa [Real.volume_real_Icc_of_le hab.le] at hm
  let Y : ℝ := 2 * (b - a) / e - 1
  have hY_ge : 1 ≤ Y := by
    dsimp [Y]
    have h2 : 2 ≤ 2 * (b - a) / e := (le_div_iff₀ he_pos).mpr (by linarith)
    linarith
  let yTarget : ℕ → ℝ := fun k => (chebNodeAsc n k + 1) / 2 * e
  have hyTarget_bounds : ∀ k ≤ n, 0 ≤ yTarget k ∧ yTarget k ≤ e := by
    intro k _
    have hnode := chebNodeAsc_mem_Icc n k
    dsimp [yTarget]
    constructor
    · nlinarith [hnode.1, he_pos]
    · nlinarith [hnode.2, he_pos]
  have hchoose : ∀ k ∈ Finset.range (n + 1),
      ∃ x ∈ K, volume.real (K ∩ Set.Icc a x) = yTarget k := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hbnd := hyTarget_bounds k (Nat.lt_succ_iff.mp hk')
    exact exists_mem_compact_measure_eq hab.le hK hKsub rfl he_pos hbnd.1 hbnd.2
  choose xPick hxPick_mem hxPick_eq using fun k : { k : ℕ // k ∈ Finset.range (n + 1) } =>
    hchoose k.1 k.2
  let xNode : ℕ → ℝ := fun k => if hk : k ∈ Finset.range (n + 1) then xPick ⟨k, hk⟩ else a
  have hxNode_K : ∀ k ∈ Finset.range (n + 1), xNode k ∈ K := by
    intro k hk
    simp only [xNode, hk, ↓reduceDIte]
    exact hxPick_mem ⟨k, hk⟩
  have hxNode_vol : ∀ k ∈ Finset.range (n + 1),
      volume.real (K ∩ Set.Icc a (xNode k)) = yTarget k := by
    intro k hk
    simp only [xNode, hk, ↓reduceDIte]
    exact hxPick_eq ⟨k, hk⟩
  have hxNode_strictMono : StrictMonoOn xNode (Finset.range (n + 1)) := by
    intro i hi j hj hij
    have ht_lt : chebNodeAsc n i < chebNodeAsc n j := chebNodeAsc_strictMonoOn n hi hj hij
    have hy_lt : yTarget i < yTarget j := by
      dsimp [yTarget]
      nlinarith [he_pos]
    by_contra hnot
    have hle : xNode j ≤ xNode i := le_of_not_gt hnot
    have hvol_le := volume_real_Icc_inter_mono K hKsub hle
    rw [hxNode_vol i hi, hxNode_vol j hj] at hvol_le
    linarith
  have hgap_lower : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1), i ≠ j →
      e / 2 * |chebNodeAsc n i - chebNodeAsc n j| ≤ |xNode i - xNode j| := by
    intro i hi j hj hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hxt : xNode i < xNode j := hxNode_strictMono hi hj hij
      have hct : chebNodeAsc n i < chebNodeAsc n j := chebNodeAsc_strictMonoOn n hi hj hij
      have hlip := volume_real_Icc_inter_lip hK.measurableSet hKsub hxt.le
      rw [hxNode_vol i hi, hxNode_vol j hj] at hlip
      have heq_y : yTarget j - yTarget i = e / 2 * (chebNodeAsc n j - chebNodeAsc n i) := by
        dsimp [yTarget]; ring
      rw [abs_sub_comm (chebNodeAsc n i), abs_sub_comm (xNode i),
        abs_of_pos (sub_pos.mpr hct), abs_of_pos (sub_pos.mpr hxt)]
      linarith
    · have hxt : xNode j < xNode i := hxNode_strictMono hj hi hji
      have hct : chebNodeAsc n j < chebNodeAsc n i := chebNodeAsc_strictMonoOn n hj hi hji
      have hlip := volume_real_Icc_inter_lip hK.measurableSet hKsub hxt.le
      rw [hxNode_vol j hj, hxNode_vol i hi] at hlip
      have heq_y : yTarget i - yTarget j = e / 2 * (chebNodeAsc n i - chebNodeAsc n j) := by
        dsimp [yTarget]; ring
      rw [abs_of_pos (sub_pos.mpr hct), abs_of_pos (sub_pos.mpr hxt)]
      linarith
  have heY : e / 2 * Y = (b - a) - e / 2 := by
    calc
      e / 2 * Y = e / 2 * (2 * (b - a) / e - 1) := rfl
      _ = (b - a) * (e / e) - e / 2 := by ring
      _ = (b - a) - e / 2 := by rw [div_self he_pos.ne', mul_one]
  have hrem_upper : ∀ i ∈ Finset.range (n + 1),
      0 ≤ b - xNode i ∧ b - xNode i ≤ e / 2 * (Y - chebNodeAsc n i) := by
    intro i hi
    have hx_Icc := hKsub (hxNode_K i hi)
    refine ⟨sub_nonneg.mpr hx_Icc.2, ?_⟩
    have hsub : K ∩ Set.Icc a (xNode i) ⊆ Set.Icc a (xNode i) := Set.inter_subset_right
    have hm := measureReal_mono hsub (by simp : volume (Set.Icc a (xNode i)) ≠ ⊤)
    rw [hxNode_vol i hi, Real.volume_real_Icc_of_le hx_Icc.1] at hm
    have hyi : e / 2 * chebNodeAsc n i = yTarget i - e / 2 := by
      dsimp [yTarget]; ring
    have hid : e / 2 * (Y - chebNodeAsc n i) = (b - a) - yTarget i := by
      rw [mul_sub, heY, hyi]; ring
    linarith
  have hPdeg : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hP_interp := Lagrange.eq_interpolate hxNode_strictMono.injOn hPdeg
  have hP_b : P.eval b =
      ∑ k ∈ Finset.range (n + 1),
        P.eval (xNode k) * (Lagrange.basis (Finset.range (n + 1)) xNode k).eval b := by
    conv_lhs => rw [hP_interp, Lagrange.interpolate_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eval_mul, eval_C]
  rw [hP_b]
  calc
    |∑ k ∈ Finset.range (n + 1),
        P.eval (xNode k) * (Lagrange.basis (Finset.range (n + 1)) xNode k).eval b|
        ≤ ∑ k ∈ Finset.range (n + 1),
            |P.eval (xNode k) * (Lagrange.basis (Finset.range (n + 1)) xNode k).eval b| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          B * ∏ i ∈ (Finset.range (n + 1)).erase k,
            ((Y - chebNodeAsc n i) / |chebNodeAsc n k - chebNodeAsc n i|) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul]
        have hPk := hKbnd (xNode k) (hxNode_K k hk)
        have hbasis_b :
            |(Lagrange.basis (Finset.range (n + 1)) xNode k).eval b| =
              ∏ i ∈ (Finset.range (n + 1)).erase k,
                ((b - xNode i) / |xNode k - xNode i|) := by
          unfold Lagrange.basis Lagrange.basisDivisor
          rw [eval_prod, Finset.abs_prod]
          refine Finset.prod_congr rfl fun i hi => ?_
          have hi_Icc := hrem_upper i (Finset.erase_subset k _ hi)
          simp only [eval_mul, eval_C, eval_sub, eval_X, abs_mul, abs_inv]
          rw [abs_of_nonneg hi_Icc.1, inv_mul_eq_div]
        rw [hbasis_b]
        refine mul_le_mul hPk ?_
          (Finset.prod_nonneg fun i hi => div_nonneg (hrem_upper i (Finset.erase_subset k _ hi)).1 (abs_nonneg _)) hB
        refine prod_le_prod_nonneg ((Finset.range (n + 1)).erase k) _ _
          (fun i hi => div_nonneg (hrem_upper i (Finset.erase_subset k _ hi)).1 (abs_nonneg _))
          (fun i hi => ?_)
        have hi_mem := Finset.mem_erase.mp hi
        have hnum := (hrem_upper i hi_mem.2).2
        have hct_ne : |chebNodeAsc n k - chebNodeAsc n i| ≠ 0 := by
          intro h0
          exact hi_mem.1 ((chebNodeAsc_strictMonoOn n).injOn hi_mem.2 hk
            (sub_eq_zero.mp (abs_eq_zero.mp h0)).symm)
        have hden_pos : 0 < e / 2 * |chebNodeAsc n k - chebNodeAsc n i| :=
          mul_pos (half_pos he_pos) (lt_of_le_of_ne (abs_nonneg _) hct_ne.symm)
        have hden := hgap_lower k hk i hi_mem.2 hi_mem.1.symm
        calc
          (b - xNode i) / |xNode k - xNode i|
              ≤ (e / 2 * (Y - chebNodeAsc n i)) / (e / 2 * |chebNodeAsc n k - chebNodeAsc n i|) :=
            div_le_div₀ (by have := (chebNodeAsc_mem_Icc n i).2; nlinarith [he_pos]) hnum hden_pos hden
          _ = (Y - chebNodeAsc n i) / |chebNodeAsc n k - chebNodeAsc n i| := by
            rw [mul_div_mul_left _ _ (by positivity)]
    _ = B * ∑ k ∈ Finset.range (n + 1),
          ∏ i ∈ (Finset.range (n + 1)).erase k,
            ((Y - chebNodeAsc n i) / |chebNodeAsc n k - chebNodeAsc n i|) := by
        rw [← Finset.mul_sum]
    _ = B * (Chebyshev.T ℝ n).eval Y := by rw [chebNodeAsc_lagrange_abs_sum n hY_ge]

private lemma remez_right_endpoint {n : ℕ} {a b B : ℝ} (hab : a < b) (hB : 0 ≤ B)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n) {E : Set ℝ} (_hEm : MeasurableSet E)
    (hEsub : E ⊆ Set.Icc a b) (he_pos : 0 < volume.real E)
    (hEbnd : ∀ t ∈ E, |P.eval t| ≤ B) :
    |P.eval b| ≤ B * (Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hP0 : P.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
    rw [Polynomial.eq_C_of_natDegree_eq_zero hP0]
    have hE_ne : E.Nonempty := by
      by_contra hEmp
      rw [Set.not_nonempty_iff_eq_empty] at hEmp
      simp [hEmp] at he_pos
    obtain ⟨t₀, ht₀⟩ := hE_ne
    have ht₀' := hEbnd t₀ ht₀
    rw [Polynomial.eq_C_of_natDegree_eq_zero hP0, eval_C] at ht₀'
    simpa using ht₀'
  · let K : Set ℝ := {t : ℝ | t ∈ Set.Icc a b ∧ |P.eval t| ≤ B}
    have hK_compact : IsCompact K :=
      isCompact_Icc.inter_right (isClosed_le P.continuous.abs continuous_const)
    have hKsub : K ⊆ Set.Icc a b := fun _ ht => ht.1
    have hEK : E ⊆ K := fun t ht => ⟨hEsub ht, hEbnd t ht⟩
    have hfinK : volume K ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono hKsub) (by simp))
    have heK_le : volume.real E ≤ volume.real K := measureReal_mono hEK hfinK
    have heK_pos : 0 < volume.real K := lt_of_lt_of_le he_pos heK_le
    have heK_upper : volume.real K ≤ b - a := by
      have hm := measureReal_mono hKsub (by simp : volume (Set.Icc a b) ≠ ⊤)
      rwa [Real.volume_real_Icc_of_le hab.le] at hm
    have hYK_ge : 1 ≤ 2 * (b - a) / volume.real K - 1 := by
      have h2 : 2 ≤ 2 * (b - a) / volume.real K := (le_div_iff₀ heK_pos).mpr (by linarith)
      linarith
    have hY_mono : 2 * (b - a) / volume.real K - 1 ≤ 2 * (b - a) / volume.real E - 1 := by
      have hdiv : 2 * (b - a) / volume.real K ≤ 2 * (b - a) / volume.real E :=
        div_le_div_of_nonneg_left (by linarith) he_pos heK_le
      linarith
    have hT_mono := chebyshev_T_mono_of_one_le n hYK_ge hY_mono
    have hcompact := remez_right_endpoint_of_compact hn hab hB P hdeg hK_compact hKsub
      heK_pos (fun _ ht => ht.2)
    exact le_trans hcompact (mul_le_mul_of_nonneg_left hT_mono hB)

end RemezCore

/-- **Full Measurable Remez Inequality:**
if `P : Polynomial ℝ` has `P.natDegree ≤ n`, `E ⊆ [a, b]` (`a < b`) is measurable
with `0 < volume.real E`, and `|P.eval t| ≤ B` for all `t ∈ E` (`0 ≤ B`), then
for every `x ∈ [a, b]`,
  `|P.eval x| ≤ (Polynomial.Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B`. -/
theorem remez_inequality (P : Polynomial ℝ) (n : ℕ) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEsub : E ⊆ Set.Icc a b)
    (he_pos : 0 < volume.real E) (hEbnd : ∀ t ∈ E, |P.eval t| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |P.eval x| ≤
      (Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B := by
  let e := volume.real E
  let EL : Set ℝ := E ∩ Set.Icc a x
  let ER : Set ℝ := E ∩ Set.Icc x b
  have hELm : MeasurableSet EL := hEm.inter measurableSet_Icc
  have hERm : MeasurableSet ER := hEm.inter measurableSet_Icc
  have hEL_sub : EL ⊆ Set.Icc a x := Set.inter_subset_right
  have hER_sub : ER ⊆ Set.Icc x b := Set.inter_subset_right
  have hfinL : volume EL ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hEL_sub) (by simp))
  have hfinR : volume ER ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hER_sub) (by simp))
  have hunion : EL ∪ ER = E := by
    have hIcc := Set.Icc_union_Icc_eq_Icc hx.1 hx.2
    rw [← Set.inter_union_distrib_left, hIcc, Set.inter_eq_left.mpr hEsub]
  have hinter : EL ∩ ER ⊆ ({x} : Set ℝ) := by
    rintro t ⟨⟨_, _, htx⟩, ⟨_, hxt, _⟩⟩
    exact le_antisymm htx hxt
  have hinter_vol : volume.real (EL ∩ ER) = 0 := by
    have h0 := measureReal_mono hinter (by simp : volume ({x} : Set ℝ) ≠ ⊤)
    simp only [Measure.real, Real.volume_singleton, ENNReal.toReal_zero] at h0
    exact le_antisymm h0 measureReal_nonneg
  have hsplit : volume.real EL + volume.real ER = e := by
    have hadd := measureReal_union_add_inter (μ := volume) hERm hfinL hfinR
    rw [hunion, hinter_vol, add_zero] at hadd
    exact hadd.symm
  have hEL_le : volume.real EL ≤ x - a := by
    have hm := measureReal_mono hEL_sub (by simp : volume (Set.Icc a x) ≠ ⊤)
    rwa [Real.volume_real_Icc_of_le hx.1] at hm
  have hER_le : volume.real ER ≤ b - x := by
    have hm := measureReal_mono hER_sub (by simp : volume (Set.Icc x b) ≠ ⊤)
    rwa [Real.volume_real_Icc_of_le hx.2] at hm
  by_cases hLeft : 0 < volume.real EL ∧ e * (x - a) ≤ volume.real EL * (b - a)
  · obtain ⟨heL_pos, hratio⟩ := hLeft
    have hax : a < x := by linarith
    have hY_left_ge : 1 ≤ 2 * (x - a) / volume.real EL - 1 := by
      have h2 : 2 ≤ 2 * (x - a) / volume.real EL := (le_div_iff₀ heL_pos).mpr (by linarith)
      linarith
    have hY_cmp : 2 * (x - a) / volume.real EL - 1 ≤ 2 * (b - a) / e - 1 := by
      have hdiv : (x - a) / volume.real EL ≤ (b - a) / e :=
        (div_le_div_iff₀ heL_pos he_pos).mpr (by linarith)
      have h2 : 2 * ((x - a) / volume.real EL) ≤ 2 * ((b - a) / e) := by linarith
      rw [← mul_div_assoc, ← mul_div_assoc] at h2
      linarith
    have hT_mono := chebyshev_T_mono_of_one_le n hY_left_ge hY_cmp
    have hre := remez_right_endpoint hax hB P hdeg hELm hEL_sub heL_pos
      (fun t ht => hEbnd t ht.1)
    rw [mul_comm B] at hre
    exact le_trans hre (mul_le_mul_of_nonneg_right hT_mono hB)
  · have hRight_pos : 0 < volume.real ER := by
      by_cases heL0 : volume.real EL = 0
      · linarith
      · have heL_gt : 0 < volume.real EL :=
          lt_of_le_of_ne measureReal_nonneg (Ne.symm heL0)
        have hnot : volume.real EL * (b - a) < e * (x - a) := by
          by_contra hle
          exact hLeft ⟨heL_gt, not_lt.mp hle⟩
        have hmul : 0 < (b - a) * volume.real ER := by
          nlinarith [hx.2, he_pos, hsplit]
        exact pos_of_mul_pos_right hmul (sub_nonneg.mpr hab.le)
    have hratioR : e * (b - x) ≤ volume.real ER * (b - a) := by
      by_cases heL0 : volume.real EL = 0
      · have heq : volume.real ER = e := by linarith
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by linarith [hx.1]) he_pos.le
      · have heL_gt : 0 < volume.real EL :=
          lt_of_le_of_ne measureReal_nonneg (Ne.symm heL0)
        have hlt : volume.real EL * (b - a) < e * (x - a) := by
          by_contra hle
          exact hLeft ⟨heL_gt, not_lt.mp hle⟩
        nlinarith [hx.1, hx.2, hsplit]
    have hxb : x < b := by linarith
    have hY_right_ge : 1 ≤ 2 * (b - x) / volume.real ER - 1 := by
      have h2 : 2 ≤ 2 * (b - x) / volume.real ER := (le_div_iff₀ hRight_pos).mpr (by linarith)
      linarith
    have hY_cmp : 2 * (b - x) / volume.real ER - 1 ≤ 2 * (b - a) / e - 1 := by
      have hdiv : (b - x) / volume.real ER ≤ (b - a) / e :=
        (div_le_div_iff₀ hRight_pos he_pos).mpr (by linarith)
      have h2 : 2 * ((b - x) / volume.real ER) ≤ 2 * ((b - a) / e) := by linarith
      rw [← mul_div_assoc, ← mul_div_assoc] at h2
      linarith
    let Q : Polynomial ℝ := P.comp (-Polynomial.X)
    let ER' : Set ℝ := (fun t : ℝ => -t) ⁻¹' ER
    have hQdeg : Q.natDegree ≤ n := by
      refine le_trans ?_ hdeg
      calc
        (P.comp (-Polynomial.X)).natDegree
            ≤ P.natDegree * (-Polynomial.X : Polynomial ℝ).natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ P.natDegree * 1 := by simp
        _ = P.natDegree := mul_one _
    have hER'm : MeasurableSet ER' := hERm.preimage continuous_neg.measurable
    have hER'_sub : ER' ⊆ Set.Icc (-b) (-x) := by
      intro t ht
      have ht' := hER_sub ht
      exact ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
    have hER'_vol : volume.real ER' = volume.real ER := by
      have hpre : ER' = ((-1 : ℝ) * ·) ⁻¹' ER := by
        ext t; simp [ER']
      rw [hpre, Measure.real, Real.volume_preimage_mul_left (a := (-1 : ℝ)) (by norm_num) ER]
      simp [Measure.real]
    have hER'_bnd : ∀ t ∈ ER', |Q.eval t| ≤ B := by
      intro t ht
      dsimp [Q]
      rw [eval_comp, eval_neg, eval_X]
      exact hEbnd (-t) ht.1
    have hre := remez_right_endpoint (by linarith : -b < -x) hB Q hQdeg hER'm hER'_sub
      (hER'_vol.symm ▸ hRight_pos) hER'_bnd
    have hQ_eval : Q.eval (-x) = P.eval x := by
      dsimp [Q]; simp [eval_comp]
    have hsub_len : (-x - -b) = b - x := by ring
    rw [hQ_eval, hsub_len, hER'_vol, mul_comm B] at hre
    have hT_mono := chebyshev_T_mono_of_one_le n hY_right_ge hY_cmp
    exact le_trans hre (mul_le_mul_of_nonneg_right hT_mono hB)

/-- **Exponential Remez Inequality on Measurable Subsets:**
if `|P| ≤ B` on a measurable subset `E ⊆ [a, b]` with `(b - a) / (1 + 1 / L) ≤ volume.real E`
(`0 < L`), then `∀ x ∈ [a, b], |P.eval x| ≤ Real.exp (2 * n / Real.sqrt L) * B`. -/
theorem remez_exponential_inequality (P : Polynomial ℝ) (n : ℕ) {a b L B : ℝ}
    (hab : a < b) (hL : 0 < L) (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEsub : E ⊆ Set.Icc a b)
    (hEmeas : (b - a) / (1 + 1 / L) ≤ volume.real E) (hEbnd : ∀ t ∈ E, |P.eval t| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |P.eval x| ≤ Real.exp (2 * (n : ℝ) / Real.sqrt L) * B := by
  have h1L_pos : 0 < 1 + 1 / L := by positivity
  have he_pos : 0 < volume.real E :=
    lt_of_lt_of_le (div_pos (sub_pos.mpr hab) h1L_pos) hEmeas
  have hE_le : volume.real E ≤ b - a := by
    have hm := measureReal_mono hEsub (by simp : volume (Set.Icc a b) ≠ ⊤)
    rwa [Real.volume_real_Icc_of_le hab.le] at hm
  have hY_ge : 1 ≤ 2 * (b - a) / volume.real E - 1 := by
    have h2 : 2 ≤ 2 * (b - a) / volume.real E := (le_div_iff₀ he_pos).mpr (by linarith)
    linarith
  have hY_le : 2 * (b - a) / volume.real E - 1 ≤ 1 + 2 / L := by
    have hdiv : (b - a) / volume.real E ≤ 1 + 1 / L := (div_le_iff₀ he_pos).mpr (by
      have hmul := mul_le_mul_of_nonneg_left hEmeas h1L_pos.le
      rw [mul_div_cancel₀ _ h1L_pos.ne'] at hmul
      linarith)
    have h2 : 2 * ((b - a) / volume.real E) ≤ 2 * (1 + 1 / L) := by linarith
    have h3 : 2 * (1 + 1 / L) = 2 + 2 / L := by ring
    rw [← mul_div_assoc, h3] at h2
    linarith
  have hT_mono := chebyshev_T_mono_of_one_le n hY_ge hY_le
  have hT_exp := chebyshev_T_one_add_two_div_le_exp n hL
  have hrem := remez_inequality P n hab hB hdeg hEm hEsub he_pos hEbnd hx
  exact le_trans hrem (mul_le_mul_of_nonneg_right (hT_mono.trans hT_exp) hB)

/-- **Combined Measurable Remez + Iterated Interior Markov Bound:**
for any `P` of degree `≤ n` bounded by `B ≥ 0` on a measurable set `E ⊆ [a, b]`
(`a < b`, `0 < volume.real E`), all `s`-th derivatives at every `x ∈ [a, b]` obey
  `|(P^(s))(x)| ≤ (2 / (b - a))^s * (∏ j < s, (n - j)^2) * T_n(2(b-a)/|E| - 1) * B`. -/
theorem remez_markov_interior_derivative_bound (P : Polynomial ℝ) (n s : ℕ) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (hdeg : P.natDegree ≤ n)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEsub : E ⊆ Set.Icc a b)
    (he_pos : 0 < volume.real E) (hEbnd : ∀ t ∈ E, |P.eval t| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |(derivative^[s] P).eval x| ≤
      (2 / (b - a)) ^ s *
        (∏ j ∈ Finset.range s, (((n - j : ℕ) : ℝ) ^ 2)) *
        ((Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B) := by
  let δ : ℝ := (b - a) / 2
  let mid : ℝ := (a + b) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  let Q : Polynomial ℝ := P.comp (C δ * X + C mid)
  have hQdeg : Q.natDegree ≤ n := by
    dsimp [Q]
    refine le_trans Polynomial.natDegree_comp_le ?_
    have hlin : (C δ * X + C mid : Polynomial ℝ).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ (by simp))
      exact le_trans (Polynomial.natDegree_C_mul_le δ X) (by simp)
    exact le_trans (Nat.mul_le_mul_left _ hlin) (by simpa using hdeg)
  have hE_le : volume.real E ≤ b - a := by
    have hm := measureReal_mono hEsub (by simp : volume (Set.Icc a b) ≠ ⊤)
    rwa [Real.volume_real_Icc_of_le hab.le] at hm
  have hY_ge : 1 ≤ 2 * (b - a) / volume.real E - 1 := by
    have h2 : 2 ≤ 2 * (b - a) / volume.real E := (le_div_iff₀ he_pos).mpr (by linarith)
    linarith
  have hT_nonneg : 0 ≤ (Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) :=
    le_trans zero_le_one (Chebyshev.one_le_eval_T_real (n : ℤ) hY_ge)
  have hM_nn : 0 ≤ (Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B :=
    mul_nonneg hT_nonneg hB
  have hQb : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |Q.eval u| ≤ (Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B := by
    intro u hu
    dsimp [Q]
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    refine remez_inequality P n hab hB hdeg hEm hEsub he_pos hEbnd ?_
    constructor <;> dsimp [δ, mid] <;> nlinarith [hu.1, hu.2, hab]
  let u : ℝ := (x - mid) / δ
  have hu_mem : u ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp [u]
    constructor
    · rw [le_div_iff₀ hδ_pos]; dsimp [δ, mid]; linarith [hx.1]
    · rw [div_le_iff₀ hδ_pos]; dsimp [δ, mid]; linarith [hx.2]
  have hQ_int := markov_iterate_derivative_interior_le Q n s hM_nn hQdeg hQb hu_mem
  have hQ_eval := iterate_derivative_affine_eval P δ mid u s
  have hux : δ * u + mid = x := by
    dsimp [u]
    field_simp [hδ_pos.ne']
    ring
  change (derivative^[s] Q).eval u = δ ^ s * (derivative^[s] P).eval (δ * u + mid) at hQ_eval
  rw [hux] at hQ_eval
  rw [hQ_eval, abs_mul, abs_of_pos (pow_pos hδ_pos s)] at hQ_int
  have hpow_pos : 0 < δ ^ s := pow_pos hδ_pos s
  have hinv_eq : (δ ^ s)⁻¹ = (2 / (b - a)) ^ s := by
    dsimp [δ]
    rw [← inv_pow, inv_div]
  have hle := mul_le_mul_of_nonneg_left hQ_int (inv_nonneg.mpr hpow_pos.le)
  calc
    |(derivative^[s] P).eval x|
        = (δ ^ s)⁻¹ * (δ ^ s * |(derivative^[s] P).eval x|) := by
          field_simp [hpow_pos.ne']
    _ ≤ (δ ^ s)⁻¹ *
          ((∏ j ∈ Finset.range s, (((n - j : ℕ) : ℝ) ^ 2)) *
            ((Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B)) := hle
    _ = (2 / (b - a)) ^ s *
          (∏ j ∈ Finset.range s, (((n - j : ℕ) : ℝ) ^ 2)) *
          ((Chebyshev.T ℝ n).eval (2 * (b - a) / volume.real E - 1) * B) := by
          rw [hinv_eq]
          ring

/-- Reciprocal samples give a uniform exponential bound on the shrinking interval. -/
theorem polynomial_reciprocal_remez_exponential_bound
    (P : Polynomial ℝ) (B : ℝ) (L m : ℕ)
    (hB : 0 < B) (hL : 0 < L) (hm : 0 < m)
    (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    ∀ x ∈ Set.Icc (0 : ℝ) (1 / ((L : ℝ) * (m : ℝ))),
      |P.eval x| ≤ Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * B := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  let E : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) (1 / ((L : ℝ) * (m : ℝ))) ∧
    |P.eval t| ≤ B}
  have hEm : MeasurableSet E :=
    measurableSet_Icc.inter (isClosed_le P.continuous.abs continuous_const).measurableSet
  have hmeasure : 1 / ((L : ℝ) * (m : ℝ) + (m : ℝ)) ≤ volume.real E := by
    simpa only [E, Nat.cast_add, Nat.cast_mul] using
      polynomial_reciprocal_good_measure P B (L * m) m hB (Nat.mul_pos hL hm)
        hdegree hsample
  have hnormalize :
      (1 / ((L : ℝ) * (m : ℝ)) - 0) / (1 + 1 / (L : ℝ)) =
        1 / ((L : ℝ) * (m : ℝ) + (m : ℝ)) := by
    field_simp [hLreal.ne', hmreal.ne', (mul_pos hLreal hmreal).ne',
      (add_pos (mul_pos hLreal hmreal) hmreal).ne']
    ring
  intro x hx
  exact remez_exponential_inequality P m (by positivity) hLreal hB.le hdegree hEm
    (fun _ ht => ht.1) (hnormalize.symm ▸ hmeasure) (fun _ ht => ht.2) hx

/-- Factorial derivative control from reciprocal samples, uniformly on the shrinking interval. -/
theorem polynomial_reciprocal_sample_factorial_bound
    (P : Polynomial ℝ) (B : ℝ) (L m s : ℕ)
    (hB : 0 < B) (hL : 0 < L) (hm : 0 < m) (hs : s ≤ m)
    (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / ((L : ℝ) * (m : ℝ)))) :
    |((derivative^[s]) P).eval x| / (s.factorial : ℝ) ≤
      (Real.exp (2 * (m : ℝ) / Real.sqrt (L : ℝ)) * B) *
        (((8 * (L : ℝ)) ^ s * (m : ℝ) ^ (3 * s)) / ((2 * s).factorial : ℝ)) := by
  have hdeg : P.degree ≤ m :=
    le_trans Polynomial.degree_le_natDegree (by exact_mod_cast hdegree)
  exact markov_reciprocal_interval_factorial_bound P m s hm hs
    (by exact_mod_cast hL) (mul_nonneg (Real.exp_pos _).le hB.le) hdeg
    (polynomial_reciprocal_remez_exponential_bound P B L m hB hL hm hdegree hsample) hx

end RhAstraSynthesis
