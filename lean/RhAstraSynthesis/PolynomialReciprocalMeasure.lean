import RhAstraSynthesis.OccupiedGap
import RhAstraSynthesis.ReciprocalGapSum
import RhAstraSynthesis.ReciprocalMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring

namespace RhAstraSynthesis

open Set MeasureTheory Filter
open scoped Topology

/-- The accumulating reciprocal samples also control the zero endpoint. -/
theorem reciprocal_node_good_zero
    (P : Polynomial ℝ) (B : ℝ)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    |P.eval 0| ≤ B := by
  have ht : Tendsto (fun n : ℕ => |P.eval (1 / (n : ℝ))|)
      atTop (𝓝 |P.eval 0|) :=
    (P.continuous.abs.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  exact le_of_tendsto ht (eventually_atTop.mpr ⟨1, fun n hn => hsample n hn⟩)

/-- Every bad point of the reciprocal interval lies strictly inside one
of its reciprocal gaps. Includes the accumulating endpoint at zero. -/
theorem bad_point_mem_reciprocal_gap
    (P : Polynomial ℝ) (B : ℝ) (k : ℕ) (hk : 0 < k)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B)
    (t : ℝ) (ht : t ∈ Icc 0 (1 / (k : ℝ))) (hbad : B < |P.eval t|) :
    ∃ j : ℕ, k ≤ j ∧ t ∈ Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ)) := by
  have htpos : 0 < t := by
    by_contra h
    have hz : t = 0 := le_antisymm (le_of_not_gt h) ht.1
    rw [hz] at hbad
    exact (not_lt_of_ge (reciprocal_node_good_zero P B hsample)) hbad
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let j : ℕ := ⌊1 / t⌋₊
  have hkt : (k : ℝ) ≤ 1 / t := by
    apply (le_div_iff₀ htpos).2
    have h := (le_div_iff₀ hkR).1 ht.2
    nlinarith
  have hkj : k ≤ j := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 1 / t)).2 hkt
  have hj : 0 < j := lt_of_lt_of_le hk hkj
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1R : (0 : ℝ) < (↑(j+1) : ℝ) := by positivity
  have hfloor : (j : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have hfloorlt : 1 / t < (j : ℝ) + 1 := Nat.lt_floor_add_one (1 / t)
  have hlow : 1 / (↑(j+1) : ℝ) < t := by
    apply (div_lt_iff₀ hj1R).2
    have h := (div_lt_iff₀ htpos).1 hfloorlt
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
  have hupper : t ≤ 1 / (j : ℝ) := by
    apply (le_div_iff₀ hjR).2
    have h := (le_div_iff₀ htpos).1 hfloor
    nlinarith
  have hstrict : t < 1 / (j : ℝ) := by
    by_contra h
    have heq : t = 1 / (j : ℝ) :=
      le_antisymm hupper (le_of_not_gt h)
    rw [heq] at hbad
    exact (not_lt_of_ge (hsample j hj)) hbad
  exact ⟨j, hkj, hlow, hstrict⟩

/-- The polynomial-specific bad-set bound: no measure estimate is assumed.
The only analytic input is the bound on all positive reciprocal samples. -/
theorem polynomial_bad_set_measure_le_gap_sum
    (P : Polynomial ℝ) (B : ℝ) (k m : ℕ) (hB : 0 < B)
    (hk : 0 < k) (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    volume.real {t : ℝ | t ∈ Icc 0 (1 / (k : ℝ)) ∧ B < |P.eval t|} ≤
      ∑ i ∈ Finset.range m, reciprocalGapLength (k+i) := by
  classical
  obtain ⟨S, hS, hcard⟩ := occupied_gaps_finite_card_le P B hB hsample
  let T := S.filter (fun j => k ≤ j)
  let J : ℕ → Set ℝ := fun j =>
    Ioo (1 / (↑(j+1) : ℝ)) (1 / (j : ℝ))
  have hT (j : ℕ) (hj : j ∈ T) : k ≤ j := (Finset.mem_filter.mp hj).2
  have hcover :
      {t : ℝ | t ∈ Icc 0 (1 / (k : ℝ)) ∧ B < |P.eval t|} ⊆
        ⋃ j ∈ T, J j := by
    intro t ht
    obtain ⟨j, hkj, htj⟩ :=
      bad_point_mem_reciprocal_gap P B k hk hsample t ht.1 ht.2
    have hjS : j ∈ S := (hS j).2 ⟨lt_of_lt_of_le hk hkj, t, htj, ht.2⟩
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hjS, hkj⟩, htj⟩⟩
  have hbounded : (⋃ j ∈ T, J j) ⊆ Icc (0 : ℝ) (1 / (k : ℝ)) := by
    intro t ht
    obtain ⟨j, hjt⟩ := mem_iUnion.mp ht
    obtain ⟨hj, htj⟩ := mem_iUnion.mp hjt
    have hkj := hT j hj
    have hjpos : 0 < j := lt_of_lt_of_le hk hkj
    have hupper : (1 : ℝ) / (j : ℝ) ≤ 1 / (k : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast hk) (by exact_mod_cast hkj)
    exact ⟨(show (0 : ℝ) < 1 / (↑(j+1) : ℝ) by positivity).le.trans htj.1.le,
      htj.2.le.trans hupper⟩
  have hlength (j : ℕ) (hj : j ∈ T) :
      volume.real (J j) = reciprocalGapLength j := by
    apply Real.volume_real_Ioo_of_le
    apply one_div_le_one_div_of_le
    · exact_mod_cast (lt_of_lt_of_le hk (hT j hj))
    · exact_mod_cast Nat.le_succ j
  have hTcard : T.card ≤ m :=
    (Finset.card_filter_le _ _).trans (hcard.trans ((Nat.sub_le _ _).trans hdegree))
  calc
    volume.real {t : ℝ | t ∈ Icc 0 (1 / (k : ℝ)) ∧ B < |P.eval t|} ≤
        volume.real (⋃ j ∈ T, J j) :=
      measureReal_mono hcover (measure_ne_top_of_subset hbounded (by simp))
    _ ≤ ∑ j ∈ T, volume.real (J j) := measureReal_biUnion_finset_le T J
    _ = ∑ j ∈ T, reciprocalGapLength j :=
      Finset.sum_congr rfl hlength
    _ ≤ ∑ i ∈ Finset.range m, reciprocalGapLength (k+i) :=
      reciprocal_gaps_sum_le_first_m T k m hk hT hTcard

/-- The full good-set estimate from polynomial degree and reciprocal samples.
In contrast with the older conditional lemma, there is no hbad premise. -/
theorem polynomial_reciprocal_good_measure
    (P : Polynomial ℝ) (B : ℝ) (k m : ℕ) (hB : 0 < B)
    (hk : 0 < k) (hdegree : P.natDegree ≤ m)
    (hsample : ∀ n : ℕ, 0 < n → |P.eval (1 / (n : ℝ))| ≤ B) :
    (1 : ℝ) / (↑(k+m) : ℝ) ≤
      volume.real {t : ℝ | t ∈ Icc 0 (1 / (k : ℝ)) ∧ |P.eval t| ≤ B} := by
  let E : Set ℝ := {t | t ∈ Icc 0 (1 / (k : ℝ)) ∧ |P.eval t| ≤ B}
  have hE : MeasurableSet E :=
    measurableSet_Icc.inter (isClosed_le P.continuous.abs continuous_const).measurableSet
  apply reciprocal_good_measure_of_bad_bound k m hk E hE (fun t ht => ht.1)
  have heq : Icc (0 : ℝ) (1 / (k : ℝ)) \ E =
      {t : ℝ | t ∈ Icc 0 (1 / (k : ℝ)) ∧ B < |P.eval t|} := by
    ext t
    change (t ∈ Icc 0 (1 / (k : ℝ)) ∧
      ¬ (t ∈ Icc 0 (1 / (k : ℝ)) ∧ |P.eval t| ≤ B)) ↔
      t ∈ Icc 0 (1 / (k : ℝ)) ∧ B < |P.eval t|
    constructor
    · rintro ⟨ht, hn⟩
      exact ⟨ht, lt_of_not_ge (fun hp => hn ⟨ht, hp⟩)⟩
    · rintro ⟨ht, hp⟩
      exact ⟨ht, fun h => (not_le_of_gt hp) h.2⟩
  rw [heq]
  exact polynomial_bad_set_measure_le_gap_sum P B k m hB hk hdegree hsample

end RhAstraSynthesis
