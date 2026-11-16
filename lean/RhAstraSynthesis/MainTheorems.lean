import RhAstraSynthesis.ChebyshevExponentialEnvelope
import RhAstraSynthesis.MarkovAffineTransport
import RhAstraSynthesis.MarkovFactorialNormalization
import RhAstraSynthesis.GevreyMomentFactorial
import RhAstraSynthesis.ActualCoprimeConvolution
import RhAstraSynthesis.CoprimeKernelSummability
import RhAstraSynthesis.CoprimeEulerMoment
import RhAstraSynthesis.MobiusHarmonicBound
import RhAstraSynthesis.MobiusExponentialTail
import RhAstraSynthesis.MellinZetaBridge
import RhAstraSynthesis.PowerKernelTransfer
import RhAstraSynthesis.PublishedEnergyBridge
import RhAstraSynthesis.VaughanIdentity
import RhAstraSynthesis.FixedDensityMellin
import RhAstraSynthesis.MarkovChebyshevGeneral
import RhAstraSynthesis.MarkovInterior
import RhAstraSynthesis.FractionalGridBounds
import RhAstraSynthesis.StieltjesTailBridge
import RhAstraSynthesis.TentOperatorObstruction
import RhAstraSynthesis.ParityAndPickObstructions

/-!
# RhAstraSynthesis — Headline Theorems

Single entry point summarizing the main verified statements in `RhAstraSynthesis`.
All declarations depend exclusively on `[propext, Classical.choice, Quot.sound]`.
-/

namespace RhAstraSynthesis.MainTheorems

open MeasureTheory Set

/-- **Reciprocal-grid good-set measure:** A degree-`≤ m` polynomial bounded by `B > 0`
at all reciprocal nodes `1/n` satisfies `|E| ≥ 1/(k + m)` on `[0, 1/k]`. -/
abbrev reciprocalGoodMeasure := @RhAstraSynthesis.polynomial_reciprocal_good_measure

/-- **Remez–Chebyshev exponential envelope:** For `1/(L*m + m) ≤ e ≤ 1/(L*m)`,
`T_m(2/(L*m*e) - 1) ≤ exp(2*m / √L)`. -/
abbrev remezChebyshevEnvelope := @RhAstraSynthesis.remez_chebyshev_T_le_exp

/-- **Cubic sharpness witness:** `P_{m,m}` has degree `≤ 2m`, satisfies `|P_{m,m}(1/n)| ≤ 1`
for all `n ≥ 1`, and attains `|P_{m,m}'(0)| ≥ 2m³ > m²`. -/
abbrev cubicSharpnessBound := @RhAstraSynthesis.reciprocalSharpnessWitness_cubic_lower_bound

/-- **Affine Markov derivative transport & Gevrey factorial cross-bound.** -/
abbrev markovAffineTransfer := @RhAstraSynthesis.markov_affine_interval_bound_transfer
abbrev gevreyFactorialBound := @RhAstraSynthesis.factorial_three_div_two_le_eight_factorial

/-- **Actual coprime Möbius factorization:** `f(n) * 1_{(n,d)=1} = (μ * g_d)(n)`. -/
abbrev coprimeMobiusFactorization := @RhAstraSynthesis.actual_coprime_mobius_factorization

/-- **Infinite Euler product for coprime kernel moments** on `s > 1/2` (`d ≠ 0`). -/
abbrev coprimeKernelEulerProduct := @RhAstraSynthesis.coprime_kernel_moment_euler_hasProd

/-- **Modulus-uniform `s = 3/4` local Euler-factor bound** (`≤ τ(d)`, including `p = 2`). -/
abbrev coprimeEulerRatioBound := @RhAstraSynthesis.finite_euler_ratio_le_divisor_count

/-- **Uniform harmonic Möbius bound:** `|∑_{1 ≤ n ≤ N} μ(n)/n| ≤ 1` for all `N ≥ 1`. -/
abbrev mobiusHarmonicBound := @RhAstraSynthesis.moebius_harmonic_abs_le_one

/-- **Laurent–exponential tail antiderivative & polynomial log-decay.** -/
abbrev mobiusTailAntideriv := @RhAstraSynthesis.mobius_tail_hasDerivAt
abbrev mobiusTailLogDecay := @RhAstraSynthesis.mobius_tail_polynomial_log_decay

/-- **Critical-strip non-vanishing of the tent Mellin multiplier** (`0 < Re(s) < 1`). -/
abbrev tentMellinNonvanishing := @TentMellin.tent_mellin_ne_zero

/-- **Prime-power Mellin–`ζ'/ζ` identity** (`1 < Re(s)`). -/
abbrev primePowerMellinZeta := @PrimePowerMellin.primePower_mellin_zeta

/-- **Lebesgue floor-kernel error bound** under `|G(t)| ≤ C t^(-γ)` (`0 < γ < 1`). -/
abbrev floorKernelErrorBound := @PowerKernelTransfer.kernel_error_bound

/-- **Generic `_root_.CommRing` signed-square coprime identity.** -/
abbrev coprimeSignedSquare := @RhAstraSynthesis.coprime_signed_square_commRing

/-- **Truncated Baez-Duarte finite L² energy shift.** -/
abbrev finiteEnergyExact := @PublishedEnergyBridge.finite_energy_exact

/-- **Vaughan Dirichlet-convolution identity** on `ArithmeticFunction ℝ`. -/
abbrev vaughanIdentity := @RhAstraSynthesis.actual_vaughan

/-- **General Chebyshev exterior growth and reciprocal endpoint Taylor Markov bound.** -/
abbrev chebyshevExteriorBound := @RhAstraSynthesis.chebyshev_exterior_eval_abs_le
abbrev reciprocalEndpointMarkov := @RhAstraSynthesis.markov_reciprocal_endpoint_factorial_bound

/-- **Bernstein / Van der Corput–Schaake & A. A. Markov interior derivative inequalities on `[-1, 1]`.** -/
abbrev bernsteinVanDerCorputSchaake := @RhAstraSynthesis.van_der_corput_schaake
abbrev markovInteriorDerivative := @RhAstraSynthesis.markov_interior_derivative_abs_le
abbrev markovIterateInteriorBound := @RhAstraSynthesis.markov_iterate_derivative_interior_le
abbrev markovInteriorIntervalTransfer := @RhAstraSynthesis.markov_interior_interval_transfer

/-- **Fractional `{n^(-α)}` Chebyshev envelope & `1/√n` (`2 m^(5/2)`) sharpness witness.** -/
abbrev fractionalRemezEnvelope := @RhAstraSynthesis.fractional_remez_chebyshev_envelope
abbrev sqrtSharpnessDerivative := @RhAstraSynthesis.sqrtSharpnessWitness_derivative_at_zero

/-- **Abel/Stieltjes summation by parts & polylogarithmic `L¹(dx/x)` tail bridge.** -/
abbrev abelSummationInv := @RhAstraSynthesis.abel_summation_inv
abbrev logDecayIntegrableTail := @RhAstraSynthesis.log_decay_integrable_and_tail_bound

/-- **Sharp `Re(s) = 1/2` tent gap & infinitely many non-outer off-axis zeros (`Re(s) ∈ (2, 4)`). -/
abbrev tentHalfLineGap := @RhAstraSynthesis.tent_numerator_half_line_lower_bound
abbrev tentOffAxisZeros := @RhAstraSynthesis.tent_numerator_infinitely_many_off_axis_zeros

/-- **Parity pseudo-density positivity, Hardy model-space defect, & `2×2` `PosSemidef` obstruction.** -/
abbrev parityPseudoDensityNonneg := @RhAstraSynthesis.parity_pseudo_density_nonneg
abbrev modelSpaceDefectLowerBound := @RhAstraSynthesis.model_space_projection_defect_lower_bound
abbrev negMinorNotPosSemidef := @RhAstraSynthesis.not_posSemidef_of_neg_two_by_two_minor

#print axioms reciprocalGoodMeasure
#print axioms remezChebyshevEnvelope
#print axioms cubicSharpnessBound
#print axioms markovAffineTransfer
#print axioms gevreyFactorialBound
#print axioms coprimeMobiusFactorization
#print axioms coprimeKernelEulerProduct
#print axioms coprimeEulerRatioBound
#print axioms mobiusHarmonicBound
#print axioms mobiusTailAntideriv
#print axioms mobiusTailLogDecay
#print axioms tentMellinNonvanishing
#print axioms primePowerMellinZeta
#print axioms floorKernelErrorBound
#print axioms coprimeSignedSquare
#print axioms finiteEnergyExact
#print axioms vaughanIdentity
#print axioms chebyshevExteriorBound
#print axioms reciprocalEndpointMarkov
#print axioms bernsteinVanDerCorputSchaake
#print axioms markovInteriorDerivative
#print axioms markovIterateInteriorBound
#print axioms markovInteriorIntervalTransfer
#print axioms fractionalRemezEnvelope
#print axioms sqrtSharpnessDerivative
#print axioms abelSummationInv
#print axioms logDecayIntegrableTail
#print axioms tentHalfLineGap
#print axioms tentOffAxisZeros
#print axioms parityPseudoDensityNonneg
#print axioms modelSpaceDefectLowerBound
#print axioms negMinorNotPosSemidef

end RhAstraSynthesis.MainTheorems
