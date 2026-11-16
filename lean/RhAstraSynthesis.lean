import RhAstraSynthesis.CoprimeMobiusSigned
import RhAstraSynthesis.CoprimeMobiusFinite
import RhAstraSynthesis.PublishedEnergyBridge
import RhAstraSynthesis.PowerKernelTransfer
import RhAstraSynthesis.TentMultiplier
import RhAstraSynthesis.TentMellin
import RhAstraSynthesis.PrimePowerMellin
import RhAstraSynthesis.ReciprocalGap
import RhAstraSynthesis.ReciprocalMeasure
import RhAstraSynthesis.ReciprocalGapOrder
import RhAstraSynthesis.OccupiedGap
import RhAstraSynthesis.ReciprocalGapSum
import RhAstraSynthesis.PolynomialReciprocalMeasure
import RhAstraSynthesis.RemezNormalization
import RhAstraSynthesis.MarkovAlgebraicFactors
import RhAstraSynthesis.MarkovFactorialNormalization
import RhAstraSynthesis.GevreyMomentFactorial
import RhAstraSynthesis.MarkovAffineTransport
import RhAstraSynthesis.MarkovChebyshevEndpoint
import RhAstraSynthesis.ReciprocalSharpnessWitness
import RhAstraSynthesis.DivisorMomentBridge
import RhAstraSynthesis.MellinZetaBridge
import RhAstraSynthesis.DensityCalibration
import RhAstraSynthesis.TentMoment
import RhAstraSynthesis.DensityMellin
import RhAstraSynthesis.FixedDensityMellin
import RhAstraSynthesis.VaughanIdentity
import RhAstraSynthesis.ChebyshevExponentialEnvelope
import RhAstraSynthesis.CoprimeFilterConvolution
import RhAstraSynthesis.ActualCoprimeConvolution
import RhAstraSynthesis.CoprimeKernelBounds
import RhAstraSynthesis.CoprimeKernelSummability
import RhAstraSynthesis.CoprimeEulerMoment
import RhAstraSynthesis.MobiusHarmonicBound
import RhAstraSynthesis.MobiusExponentialTail
import RhAstraSynthesis.MarkovChebyshevGeneral
import RhAstraSynthesis.MarkovInterior
import RhAstraSynthesis.FractionalGridBounds
import RhAstraSynthesis.StieltjesTailBridge
import RhAstraSynthesis.TentOperatorObstruction
import RhAstraSynthesis.ParityAndPickObstructions
import RhAstraSynthesis.MainTheorems

/-!
  Canonical Lean 4 root module for `RhAstraSynthesis`, aggregating all 42
  submodules (see `RhAstraSynthesis.MainTheorems` for the headline theorem index):
  - Reciprocal-lattice geometry & occupied-gap measure bounds,
  - A. A. Markov 1889 interior derivative inequality, Van der Corput–Schaake inequality, endpoint/exterior/affine Markov bounds, exponential Remez envelope & Gevrey-1 scaling,
  - Fractional-grid `{n^(-α)}` Remez envelope & `1/√n` (`2 m^(5/2)`) sharpness witness,
  - Extremal reciprocal-grid cubic sharpness witness,
  - Finite Baez-Duarte energy shifts & coprime Möbius quadratic factorizations,
  - Power-decay and polylogarithmic Stieltjes floor-kernel Lebesgue integral bounds,
  - Tent-kernel Mellin non-vanishing, sharp critical-line lower bound, non-outer off-axis zeros, calibrated mixture Mellin & ζ'/ζ identities,
  - Parity pseudo-density, Hardy model-space defect, and `PosSemidef` minor obstructions,
  - Vaughan Dirichlet-convolution identity,
  - Modulus-uniform `s = 3/4` Euler-factor, coprime-filter envelope & `τ(n)^2 ≤ d_4(n)` arithmetic bridges,
  - Actual coprime Möbius kernel factorization, pointwise majorants, `s > 1/2` Euler-product summability, and finite moment transfers,
  - Uniform harmonic Möbius partial-sum bound `|∑_{n ≤ N} μ(n)/n| ≤ 1` and Laurent-exponential tail decay.
-/
