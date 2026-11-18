import Mathematics212.ReciprocalGap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# A conditional lower bound on the good set's Lebesgue measure

This module formalizes the **implication** in equation (4) of the pinned
Gevrey-1 reciprocal-sampling proof: if the bad set has measure no larger
than the sum of the first `m` reciprocal gaps, then the good set has
measure at least `1/(k+m)`.

The central *polynomial-specific* inequality estimating the bad set
from the critical points of `P` is NOT proved here. It remains a
separate dependency and must not be inferred from this lemma.
-/

open MeasureTheory

namespace Mathematics212

/--
Conditional measure consequence of equation (4).
The set `E` is any measurable subset of `[0,1/k]`, not necessarily
constructed from a polynomial.
-/
theorem reciprocal_good_measure_of_bad_bound
    (k m : ℕ) (hk : 0 < k)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Icc (0 : ℝ) (1 / (k : ℝ)))
    (hbad :
      volume.real (Set.Icc (0 : ℝ) (1 / (k : ℝ)) \ E) ≤
        ∑ j ∈ Finset.range m,
          ((1 : ℝ) / (↑(k + j) : ℝ) -
            (1 : ℝ) / (↑(k + j + 1) : ℝ))) :
    (1 : ℝ) / (↑(k + m) : ℝ) ≤ volume.real E := by
  let I : Set ℝ := Set.Icc (0 : ℝ) (1 / (k : ℝ))
  have hIle : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hfinite : volume I ≠ ⊤ := by
    dsimp [I]
    simp
  have hpartition :
      volume.real E + volume.real (I \ E) = 1 / (k : ℝ) := by
    have h := measureReal_inter_add_sdiff (μ := volume)
      (s := I) (t := E) hE hfinite
    have hint : I ∩ E = E := Set.inter_eq_right.mpr hEsub
    rw [hint] at h
    rw [Real.volume_real_Icc_of_le hIle] at h
    simpa [I] using h
  have hbad' :
      volume.real (I \ E) ≤
        (1 : ℝ) / (k : ℝ) - (1 : ℝ) / (↑(k + m) : ℝ) := by
    change volume.real (I \ E) ≤ _ at hbad
    simpa only [reciprocal_gap_telescope k m hk] using hbad
  linarith

end Mathematics212
