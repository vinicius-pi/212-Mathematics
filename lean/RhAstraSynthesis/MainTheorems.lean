import RhAstraSynthesis.ChebyshevExponentialEnvelope
import RhAstraSynthesis.MarkovAffineTransport
import RhAstraSynthesis.MarkovFactorialNormalization
import RhAstraSynthesis.GevreyMomentFactorial
import RhAstraSynthesis.ReciprocalGevreyMajorant
import RhAstraSynthesis.ReciprocalCoefficientProfile
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
import RhAstraSynthesis.RemezInequality
import RhAstraSynthesis.FractionalGridBounds
import RhAstraSynthesis.StieltjesTailBridge
import RhAstraSynthesis.TentOperatorObstruction
import RhAstraSynthesis.ParityAndPickObstructions

/-!
# Headline Theorems

Single index of main results across Sections I–III of `RhAstraSynthesis`.
All declarations use only `[propext, Classical.choice, Quot.sound]`;
see `RhAstraSynthesis.TargetStatements` for self-contained signatures and examples.
-/

namespace RhAstraSynthesis.MainTheorems

-- §1. Polynomial Approximation, Bernstein & Markov–Remez Bounds

abbrev bernsteinVanDerCorputSchaake := @RhAstraSynthesis.van_der_corput_schaake
abbrev markovInteriorDerivative := @RhAstraSynthesis.markov_interior_derivative_abs_le
abbrev markovIterateInteriorBound := @RhAstraSynthesis.markov_iterate_derivative_interior_le
abbrev markovInteriorIntervalTransfer := @RhAstraSynthesis.markov_interior_interval_transfer
abbrev remezInequality := @RhAstraSynthesis.remez_inequality
abbrev remezExponentialInequality := @RhAstraSynthesis.remez_exponential_inequality
abbrev remezMarkovInteriorBound := @RhAstraSynthesis.remez_markov_interior_derivative_bound
abbrev chebyshevExteriorBound := @RhAstraSynthesis.chebyshev_exterior_eval_abs_le
abbrev reciprocalEndpointMarkov := @RhAstraSynthesis.markov_reciprocal_endpoint_factorial_bound
abbrev reciprocalGoodMeasure := @RhAstraSynthesis.polynomial_reciprocal_good_measure
abbrev remezChebyshevEnvelope := @RhAstraSynthesis.remez_chebyshev_T_le_exp
abbrev markovAffineTransfer := @RhAstraSynthesis.markov_affine_interval_bound_transfer
abbrev gevreyFactorialBound := @RhAstraSynthesis.factorial_three_div_two_le_eight_factorial
abbrev reciprocalGevreyMajorant := @RhAstraSynthesis.cubic_geometric_gevrey_majorant
abbrev reciprocalComplexProfiles := @RhAstraSynthesis.polynomial_reciprocal_profiles_all_radii
abbrev cubicSharpnessBound := @RhAstraSynthesis.reciprocalSharpnessWitness_cubic_lower_bound
abbrev fractionalRemezEnvelope := @RhAstraSynthesis.fractional_remez_chebyshev_envelope
abbrev sqrtSharpnessDerivative := @RhAstraSynthesis.sqrtSharpnessWitness_derivative_at_zero

-- §2. Multiplicative Convolutions, Euler Products & Arithmetic Identities

abbrev coprimeMobiusFactorization := @RhAstraSynthesis.actual_coprime_mobius_factorization
abbrev coprimeKernelEulerProduct := @RhAstraSynthesis.coprime_kernel_moment_euler_hasProd
abbrev coprimeEulerRatioBound := @RhAstraSynthesis.finite_euler_ratio_le_divisor_count
abbrev mobiusHarmonicBound := @RhAstraSynthesis.moebius_harmonic_abs_le_one
abbrev mobiusTailAntideriv := @RhAstraSynthesis.mobius_tail_hasDerivAt
abbrev mobiusTailLogDecay := @RhAstraSynthesis.mobius_tail_polynomial_log_decay
abbrev coprimeSignedSquare := @RhAstraSynthesis.coprime_signed_square_commRing
abbrev finiteEnergyExact := @PublishedEnergyBridge.finite_energy_exact
abbrev vaughanIdentity := @RhAstraSynthesis.actual_vaughan

-- §3. Mellin Multipliers, Stieltjes Tails & Integral Obstructions

abbrev tentMellinNonvanishing := @TentMellin.tent_mellin_ne_zero
abbrev primePowerMellinZeta := @PrimePowerMellin.primePower_mellin_zeta
abbrev floorKernelErrorBound := @PowerKernelTransfer.kernel_error_bound
abbrev abelSummationInv := @RhAstraSynthesis.abel_summation_inv
abbrev logDecayIntegrableTail := @RhAstraSynthesis.log_decay_integrable_and_tail_bound
abbrev tentHalfLineGap := @RhAstraSynthesis.tent_numerator_half_line_lower_bound
abbrev tentOffAxisZeros := @RhAstraSynthesis.tent_numerator_infinitely_many_off_axis_zeros
abbrev parityPseudoDensityNonneg := @RhAstraSynthesis.parity_pseudo_density_nonneg
abbrev modelSpaceDefectLowerBound := @RhAstraSynthesis.model_space_projection_defect_lower_bound
abbrev negMinorNotPosSemidef := @RhAstraSynthesis.not_posSemidef_of_neg_two_by_two_minor

#print axioms bernsteinVanDerCorputSchaake
#print axioms markovInteriorDerivative
#print axioms markovIterateInteriorBound
#print axioms markovInteriorIntervalTransfer
#print axioms remezInequality
#print axioms remezExponentialInequality
#print axioms remezMarkovInteriorBound
#print axioms chebyshevExteriorBound
#print axioms reciprocalEndpointMarkov
#print axioms reciprocalGoodMeasure
#print axioms remezChebyshevEnvelope
#print axioms markovAffineTransfer
#print axioms gevreyFactorialBound
#print axioms reciprocalGevreyMajorant
#print axioms reciprocalComplexProfiles
#print axioms cubicSharpnessBound
#print axioms fractionalRemezEnvelope
#print axioms sqrtSharpnessDerivative
#print axioms coprimeMobiusFactorization
#print axioms coprimeKernelEulerProduct
#print axioms coprimeEulerRatioBound
#print axioms mobiusHarmonicBound
#print axioms mobiusTailAntideriv
#print axioms mobiusTailLogDecay
#print axioms coprimeSignedSquare
#print axioms finiteEnergyExact
#print axioms vaughanIdentity
#print axioms tentMellinNonvanishing
#print axioms primePowerMellinZeta
#print axioms floorKernelErrorBound
#print axioms abelSummationInv
#print axioms logDecayIntegrableTail
#print axioms tentHalfLineGap
#print axioms tentOffAxisZeros
#print axioms parityPseudoDensityNonneg
#print axioms modelSpaceDefectLowerBound
#print axioms negMinorNotPosSemidef

end RhAstraSynthesis.MainTheorems
