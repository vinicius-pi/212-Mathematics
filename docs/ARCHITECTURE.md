# Architecture & Module Inventory

`RhAstraSynthesis` (`leanprover/lean4:v4.34.0`, `mathlib@5ed2965256430c3649e86755f9576b54eca72435`) is organized into four functional groups across 42 submodules, indexed through `RhAstraSynthesis.MainTheorems`. This document summarizes the module responsibilities across analysis, arithmetic, operator theory, and algebraic infrastructure.

## 1. Reciprocal- and Fractional-Grid Polynomial Analysis (17 modules)

- **Measure reduction:** `ReciprocalGap`, `ReciprocalMeasure`, `ReciprocalGapOrder`, `OccupiedGap`, `ReciprocalGapSum`, `PolynomialReciprocalMeasure` — Rolle-based bad-gap counting and Lebesgue measure lower bound `|E| ≥ 1/(k + m)` on `[0, 1/k]`.
- **Chebyshev–Remez envelope:** `RemezNormalization`, `ChebyshevExponentialEnvelope` — `remez_argument_of_measure` and `remez_chebyshev_T_le_exp` (`T_m(1 + 2/L) ≤ exp(2m/√L)`).
- **Markov–Gevrey scalings, Bernstein & interior Markov:** `MarkovAlgebraicFactors`, `MarkovFactorialNormalization`, `GevreyMomentFactorial`, `MarkovAffineTransport`, `MarkovChebyshevEndpoint`, `MarkovChebyshevGeneral`, `MarkovInterior` — affine derivative chain rule, endpoint Markov saturation at `±1`, scaled exterior bound `|P(x)| ≤ B T_m(|x|)` (`|x| ≥ 1`), full Bernstein / Van der Corput–Schaake inequality `n² P(cos θ)² + (P'(cos θ) sin θ)² ≤ n² B²`, A. A. Markov's 1889 interior derivative bound `|P'(x)| ≤ n² B` on `[-1, 1]` and its `s`-fold iteration `∏_{j < s} (n - j)² B`, unconditional endpoint and interior transports to `[0, 1/(Lm)]`, and `(3k)!/(2k)! ≤ 8^k k!`.
- **Fractional-grid analysis & sharpness:** `ReciprocalSharpnessWitness`, `FractionalGridBounds` — `{1/n}` cubic witness `|P_{m,m}'(0)| ≥ 2m³ > m²`, `{n^(-α)}` gap monotonicity/telescoping, Bernoulli–Chebyshev envelope `exp(2m√(α/L))`, and `1/√n` witness `|Q_{m,m}'(0)| ≥ 2m^(5/2) > m²`.

## 2. Coprime Möbius Convolution, Summability & Divisor Moments (8 modules)

- **Core analytic & Euler-product chain:** `ActualCoprimeConvolution`, `CoprimeKernelBounds`, `CoprimeKernelSummability`, `DivisorMomentBridge`, `CoprimeEulerMoment` — multiplicative kernel `g_d(n) = ψ(gcd(n,d))/ψ(n)`, `f(n)1_{(n,d)=1} = (μ * g_d)(n)`, `HasProd` convergence for `s > 1/2`, `τ(p^e)² ≤ d_4(p^e)`, and `< 2` local Euler-factor bounds at `s = 3/4` (including `p = 2` with `r_2 = 2/3`).
- **Elementary & real-analytic bounds:** `MobiusHarmonicBound` (`|∑_{n≤N} μ(n)/n| ≤ 1`), `MobiusExponentialTail` (exact Laurent–exponential antiderivative and Taylor decay), `CoprimeFilterConvolution` (`r(d) ∈ (0, 1]`, elementary quadratic split).

## 3. Tent-Kernel Mellin, Stieltjes Tails & Obstruction Theorems (11 modules)

- **Critical-strip Mellin, `ζ'/ζ`, & non-outer off-axis zeros:** `TentMultiplier`, `TentMellin`, `PrimePowerMellin`, `TentOperatorObstruction` — proves `mellin tent s ≠ 0` on `0 < Re(s) < 1`, the sharp `Re(s) = 1/2` lower bound `√3 - 1 - 1/√2`, the prime-power `-\zeta'(s)/\zeta(s)` identity on `1 < Re(s)`, and infinitely many zeros of `TentMultiplier.numerator` in `2 < Re(s) < 4` with `R < Im(s)`.
- **Logarithmic calibration:** `DensityCalibration`, `TentMoment`, `DensityMellin`, `FixedDensityMellin` — rational interval bounds for `log(4/3)` and `log 2` and calibrated mixture weights in `(0, 1)`.
- **Floor-kernel & Stieltjes polylogarithmic tails:** `PowerKernelTransfer`, `StieltjesTailBridge` — exact floor-kernel remainder identity under `|G(t)| ≤ C t^(-γ)`, `80/89` minimax envelope, finite Abel/Stieltjes summation by parts, and `|G(t)| ≤ C (log t)^(-1-δ) ⇒ G(t)/t ∈ L¹([2, ∞))`.
- **Structural obstructions:** `ParityAndPickObstructions` — non-negativity of Selberg parity pseudo-densities `1 + t^(-1/4) cos(ω log t)`, Hardy model-space defect lower bound `(2 Re z - 1)/‖z‖² > 0`, and `2 × 2` principal-minor refutation of `Matrix.PosSemidef`.

## 4. Finite Algebraic Plumbing & Headline Index (6 modules)

- `CoprimeMobiusFinite`, `CoprimeMobiusSigned`, `MellinZetaBridge` — finite Möbius-inversion signed-square identities (`_root_.CommRing` typeclass hygiene avoiding `Lean.Grind.CommRing` collisions) and Mellin–`ζ'/ζ` interface exports.
- `PublishedEnergyBridge` — finite Baez–Duarte truncated `L²` shift identity `E_tail = E_trunc - 1` formalized directly over Mathlib's `ArithmeticFunction.moebius`.
- `VaughanIdentity` — finite Vaughan Dirichlet-convolution identity on `ArithmeticFunction ℝ`.
- `MainTheorems` — single-entry summary module aliasing the core theorems across Sections 1–4 with `#print axioms` checks.
