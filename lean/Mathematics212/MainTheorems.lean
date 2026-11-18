import Mathematics212.ChebyshevExponentialEnvelope
import Mathematics212.MarkovAffineTransport
import Mathematics212.MarkovFactorialNormalization
import Mathematics212.GevreyMomentFactorial
import Mathematics212.ReciprocalGevreyMajorant
import Mathematics212.ReciprocalCoefficientProfile
import Mathematics212.ReciprocalTaylorRemainder
import Mathematics212.ReciprocalRemainderSeries
import Mathematics212.ReciprocalGevreyExpansion
import Mathematics212.ActualCoprimeConvolution
import Mathematics212.CoprimeKernelSummability
import Mathematics212.CoprimeEulerMoment
import Mathematics212.MobiusHarmonicBound
import Mathematics212.MobiusExponentialTail
import Mathematics212.MellinZetaBridge
import Mathematics212.PowerKernelTransfer
import Mathematics212.PublishedEnergyBridge
import Mathematics212.VaughanIdentity
import Mathematics212.FixedDensityMellin
import Mathematics212.MarkovChebyshevGeneral
import Mathematics212.MarkovInterior
import Mathematics212.RemezInequality
import Mathematics212.FractionalGridBounds
import Mathematics212.StieltjesTailBridge
import Mathematics212.TentOperatorObstruction
import Mathematics212.ParityAndPickObstructions

/-!
# Headline Theorems

Single index of main results across Sections I–III of `Mathematics212`.
All declarations use only `[propext, Classical.choice, Quot.sound]`;
see `Mathematics212.TargetStatements` for self-contained signatures and examples.
-/

namespace Mathematics212.MainTheorems

-- §1. Polynomial Approximation, Bernstein & Markov–Remez Bounds

abbrev bernsteinVanDerCorputSchaake := @Mathematics212.van_der_corput_schaake
abbrev markovInteriorDerivative := @Mathematics212.markov_interior_derivative_abs_le
abbrev markovIterateInteriorBound := @Mathematics212.markov_iterate_derivative_interior_le
abbrev markovInteriorIntervalTransfer := @Mathematics212.markov_interior_interval_transfer
abbrev remezInequality := @Mathematics212.remez_inequality
abbrev remezExponentialInequality := @Mathematics212.remez_exponential_inequality
abbrev remezMarkovInteriorBound := @Mathematics212.remez_markov_interior_derivative_bound
abbrev chebyshevExteriorBound := @Mathematics212.chebyshev_exterior_eval_abs_le
abbrev reciprocalEndpointMarkov := @Mathematics212.markov_reciprocal_endpoint_factorial_bound
abbrev reciprocalGoodMeasure := @Mathematics212.polynomial_reciprocal_good_measure
abbrev remezChebyshevEnvelope := @Mathematics212.remez_chebyshev_T_le_exp
abbrev markovAffineTransfer := @Mathematics212.markov_affine_interval_bound_transfer
abbrev gevreyFactorialBound := @Mathematics212.factorial_three_div_two_le_eight_factorial
abbrev reciprocalGevreyMajorant := @Mathematics212.cubic_geometric_gevrey_majorant
abbrev reciprocalComplexProfiles := @Mathematics212.polynomial_reciprocal_profiles_all_radii
abbrev reciprocalProfilesHolomorphic := @Mathematics212.polynomial_reciprocal_profiles_holomorphic
abbrev reciprocalTaylorRemainder := @Mathematics212.polynomial_reciprocal_taylor_remainder_bound
abbrev reciprocalAbsoluteRemainderSeries := @Mathematics212.polynomial_reciprocal_family_remainder_gevrey
abbrev reciprocalGevreyExpansion := @Mathematics212.polynomial_reciprocal_gevrey_expansion
abbrev cubicSharpnessBound := @Mathematics212.reciprocalSharpnessWitness_cubic_lower_bound
abbrev fractionalRemezEnvelope := @Mathematics212.fractional_remez_chebyshev_envelope
abbrev sqrtSharpnessDerivative := @Mathematics212.sqrtSharpnessWitness_derivative_at_zero

-- §2. Multiplicative Convolutions, Euler Products & Arithmetic Identities

abbrev coprimeMobiusFactorization := @Mathematics212.actual_coprime_mobius_factorization
abbrev coprimeKernelEulerProduct := @Mathematics212.coprime_kernel_moment_euler_hasProd
abbrev coprimeEulerRatioBound := @Mathematics212.finite_euler_ratio_le_divisor_count
abbrev mobiusHarmonicBound := @Mathematics212.moebius_harmonic_abs_le_one
abbrev mobiusTailAntideriv := @Mathematics212.mobius_tail_hasDerivAt
abbrev mobiusTailLogDecay := @Mathematics212.mobius_tail_polynomial_log_decay
abbrev coprimeSignedSquare := @Mathematics212.coprime_signed_square_commRing
abbrev finiteEnergyExact := @PublishedEnergyBridge.finite_energy_exact
abbrev vaughanIdentity := @Mathematics212.actual_vaughan

-- §3. Mellin Multipliers, Stieltjes Tails & Integral Obstructions

abbrev tentMellinNonvanishing := @TentMellin.tent_mellin_ne_zero
abbrev primePowerMellinZeta := @PrimePowerMellin.primePower_mellin_zeta
abbrev floorKernelErrorBound := @PowerKernelTransfer.kernel_error_bound
abbrev abelSummationInv := @Mathematics212.abel_summation_inv
abbrev logDecayIntegrableTail := @Mathematics212.log_decay_integrable_and_tail_bound
abbrev tentHalfLineGap := @Mathematics212.tent_numerator_half_line_lower_bound
abbrev tentOffAxisZeros := @Mathematics212.tent_numerator_infinitely_many_off_axis_zeros
abbrev parityPseudoDensityNonneg := @Mathematics212.parity_pseudo_density_nonneg
abbrev modelSpaceDefectLowerBound := @Mathematics212.model_space_projection_defect_lower_bound
abbrev negMinorNotPosSemidef := @Mathematics212.not_posSemidef_of_neg_two_by_two_minor

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
#print axioms reciprocalProfilesHolomorphic
#print axioms reciprocalTaylorRemainder
#print axioms reciprocalAbsoluteRemainderSeries
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

end Mathematics212.MainTheorems
