-- I. Polynomial Approximation, Bernstein & Markov–Remez Bounds
import Mathematics212.ReciprocalGap
import Mathematics212.ReciprocalGapOrder
import Mathematics212.ReciprocalMeasure
import Mathematics212.OccupiedGap
import Mathematics212.ReciprocalGapSum
import Mathematics212.PolynomialReciprocalMeasure
import Mathematics212.RemezNormalization
import Mathematics212.ChebyshevExponentialEnvelope
import Mathematics212.MarkovAlgebraicFactors
import Mathematics212.MarkovFactorialNormalization
import Mathematics212.GevreyMomentFactorial
import Mathematics212.ReciprocalGevreyMajorant
import Mathematics212.ReciprocalCoefficientProfile
import Mathematics212.ReciprocalTaylorRemainder
import Mathematics212.ReciprocalRemainderSeries
import Mathematics212.ReciprocalGevreyExpansion
import Mathematics212.MarkovAffineTransport
import Mathematics212.MarkovChebyshevEndpoint
import Mathematics212.MarkovChebyshevGeneral
import Mathematics212.MarkovInterior
import Mathematics212.RemezInequality
import Mathematics212.ReciprocalSharpnessWitness
import Mathematics212.FractionalGridBounds

-- II. Multiplicative Convolutions, Euler Products & Arithmetic Identities
import Mathematics212.CoprimeMobiusSigned
import Mathematics212.CoprimeMobiusFinite
import Mathematics212.PublishedEnergyBridge
import Mathematics212.VaughanIdentity
import Mathematics212.CoprimeFilterConvolution
import Mathematics212.ActualCoprimeConvolution
import Mathematics212.CoprimeKernelBounds
import Mathematics212.CoprimeKernelSummability
import Mathematics212.DivisorMomentBridge
import Mathematics212.CoprimeEulerMoment
import Mathematics212.MobiusHarmonicBound
import Mathematics212.MobiusExponentialTail

-- III. Mellin Multipliers, Stieltjes Tails & Integral Obstructions
import Mathematics212.PowerKernelTransfer
import Mathematics212.StieltjesTailBridge
import Mathematics212.TentMultiplier
import Mathematics212.TentMellin
import Mathematics212.PrimePowerMellin
import Mathematics212.MellinZetaBridge
import Mathematics212.DensityCalibration
import Mathematics212.TentMoment
import Mathematics212.DensityMellin
import Mathematics212.FixedDensityMellin
import Mathematics212.TentOperatorObstruction
import Mathematics212.ParityAndPickObstructions

-- IV. Target Interfaces & Headline Index
import Mathematics212.MainTheorems
import Mathematics212.TargetStatements

/-!
  Root module for `Mathematics212`, importing the mathematical submodules
  (see `Mathematics212.MainTheorems` and `Mathematics212.TargetStatements`
  for the headline theorem index and concrete examples):

  I. Polynomial Approximation, Bernstein & Markov–Remez Bounds
     - Reciprocal- and fractional-grid `{n^(-α)}` measure reductions,
     - Bernstein / Van der Corput–Schaake inequality, A. A. Markov's 1889 interior bound, and the full measurable equioscillation Remez inequality,
     - Markov–Chebyshev endpoint/exterior/affine derivative bounds and exponential Remez envelopes,
     - Explicit cubic (`2m^3`) and `1/√n` (`2m^(5/2)`) sharpness witnesses.

  II. Multiplicative Convolutions, Euler Products & Arithmetic Identities
     - Actual coprime Möbius factorization, `s > 1/2` Euler-product convergence,
     - Modulus-uniform `s = 3/4` local Euler-factor bounds (`< 2` including `p = 2`),
     - Uniform harmonic Möbius partial-sum bound `|∑_{n ≤ N} μ(n)/n| ≤ 1`,
     - Finite Baez–Duarte `L²` shifts, signed-square ring identities, and Vaughan's identity.

  III. Mellin Multipliers, Stieltjes Tails & Integral Obstructions
     - Tent-kernel Mellin critical-strip non-vanishing, sharp `Re(s) = 1/2` gap,
       and infinitely many non-outer off-axis zeros in `2 < Re(s) < 4`,
     - Prime-power `ζ'/ζ` identity and calibrated logarithmic mixture bounds,
     - Lebesgue floor-kernel and polylogarithmic Stieltjes `L¹(dx/x)` tail transfers,
     - Selberg parity pseudo-densities, Hardy model-space defects, and `2 × 2` Pick obstructions.
-/
