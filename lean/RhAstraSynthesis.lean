-- I. Polynomial Approximation, Bernstein & Markov–Remez Bounds
import RhAstraSynthesis.ReciprocalGap
import RhAstraSynthesis.ReciprocalGapOrder
import RhAstraSynthesis.ReciprocalMeasure
import RhAstraSynthesis.OccupiedGap
import RhAstraSynthesis.ReciprocalGapSum
import RhAstraSynthesis.PolynomialReciprocalMeasure
import RhAstraSynthesis.RemezNormalization
import RhAstraSynthesis.ChebyshevExponentialEnvelope
import RhAstraSynthesis.MarkovAlgebraicFactors
import RhAstraSynthesis.MarkovFactorialNormalization
import RhAstraSynthesis.GevreyMomentFactorial
import RhAstraSynthesis.ReciprocalGevreyMajorant
import RhAstraSynthesis.ReciprocalCoefficientProfile
import RhAstraSynthesis.ReciprocalTaylorRemainder
import RhAstraSynthesis.MarkovAffineTransport
import RhAstraSynthesis.MarkovChebyshevEndpoint
import RhAstraSynthesis.MarkovChebyshevGeneral
import RhAstraSynthesis.MarkovInterior
import RhAstraSynthesis.RemezInequality
import RhAstraSynthesis.ReciprocalSharpnessWitness
import RhAstraSynthesis.FractionalGridBounds

-- II. Multiplicative Convolutions, Euler Products & Arithmetic Identities
import RhAstraSynthesis.CoprimeMobiusSigned
import RhAstraSynthesis.CoprimeMobiusFinite
import RhAstraSynthesis.PublishedEnergyBridge
import RhAstraSynthesis.VaughanIdentity
import RhAstraSynthesis.CoprimeFilterConvolution
import RhAstraSynthesis.ActualCoprimeConvolution
import RhAstraSynthesis.CoprimeKernelBounds
import RhAstraSynthesis.CoprimeKernelSummability
import RhAstraSynthesis.DivisorMomentBridge
import RhAstraSynthesis.CoprimeEulerMoment
import RhAstraSynthesis.MobiusHarmonicBound
import RhAstraSynthesis.MobiusExponentialTail

-- III. Mellin Multipliers, Stieltjes Tails & Integral Obstructions
import RhAstraSynthesis.PowerKernelTransfer
import RhAstraSynthesis.StieltjesTailBridge
import RhAstraSynthesis.TentMultiplier
import RhAstraSynthesis.TentMellin
import RhAstraSynthesis.PrimePowerMellin
import RhAstraSynthesis.MellinZetaBridge
import RhAstraSynthesis.DensityCalibration
import RhAstraSynthesis.TentMoment
import RhAstraSynthesis.DensityMellin
import RhAstraSynthesis.FixedDensityMellin
import RhAstraSynthesis.TentOperatorObstruction
import RhAstraSynthesis.ParityAndPickObstructions

-- IV. Target Interfaces & Headline Index
import RhAstraSynthesis.MainTheorems
import RhAstraSynthesis.TargetStatements

/-!
  Root module for `RhAstraSynthesis`, importing the mathematical submodules
  (see `RhAstraSynthesis.MainTheorems` and `RhAstraSynthesis.TargetStatements`
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
