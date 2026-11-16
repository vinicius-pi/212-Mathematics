# Architecture & Module Inventory

`RhAstraSynthesis` (`leanprover/lean4:v4.34.0`, `mathlib@5ed2965256430c3649e86755f9576b54eca72435`) organizes 44 submodules into four groups indexed through [`MainTheorems.lean`](../lean/RhAstraSynthesis/MainTheorems.lean) and [`TargetStatements.lean`](../lean/RhAstraSynthesis/TargetStatements.lean).

## 1. Polynomial Approximation, Bernstein & Markov–Remez Bounds (18 modules)

- **Reciprocal-grid measure reduction:** `ReciprocalGap`, `ReciprocalMeasure`, `ReciprocalGapOrder`, `OccupiedGap`, `ReciprocalGapSum`, `PolynomialReciprocalMeasure` — Rolle-based bad-gap counting and Lebesgue measure bound `|E| ≥ 1/(k + m)` on `[0, 1/k]`.
- **Measurable Remez inequality & exponential envelope:** `RemezNormalization`, `ChebyshevExponentialEnvelope`, `RemezInequality` — `remez_argument_of_measure`, `remez_chebyshev_T_le_exp` (`T_m(1 + 2/L) ≤ exp(2m/√L)`), full measurable equioscillation Remez bound `|P(x)| ≤ T_n(2(b-a)/|E| - 1) B` via Bojanov's Lagrange–Chebyshev node-selection proof, exponential Remez corollary `|P(x)| ≤ exp(2n/√L) B`, and combined Remez + iterated Markov interior derivative bound `|P^(s)(x)| ≤ (2/(b-a))^s (∏_{j<s} (n-j)^2) T_n(2(b-a)/|E| - 1) B`.
- **Bernstein, interior Markov & Gevrey scalings:** `MarkovAlgebraicFactors`, `MarkovFactorialNormalization`, `GevreyMomentFactorial`, `MarkovAffineTransport`, `MarkovChebyshevEndpoint`, `MarkovChebyshevGeneral`, `MarkovInterior` — affine derivative chain rule, endpoint Markov saturation at `±1`, scaled exterior bound `|P(x)| ≤ B T_m(|x|)` (`|x| ≥ 1`), Bernstein / Van der Corput–Schaake inequality `n² P(cos θ)² + (P'(cos θ) sin θ)² ≤ n² B²`, A. A. Markov's 1889 interior bound `|P'(x)| ≤ n² B` on `[-1, 1]` with `s`-fold iteration `∏_{j < s} (n - j)² B`, unconditional endpoint and interior transports to `[0, 1/(Lm)]`, and `(3k)!/(2k)! ≤ 8^k k!`.
- **Fractional-grid analysis & sharpness witnesses:** `ReciprocalSharpnessWitness`, `FractionalGridBounds` — `{1/n}` cubic witness `|P_{m,m}'(0)| ≥ 2m³ > m²`, `{n^(-α)}` gap monotonicity and telescoping, Bernoulli–Chebyshev envelope `exp(2m√(α/L))`, and `1/√n` witness `|Q_{m,m}'(0)| ≥ 2m^(5/2) > m²`.

## 2. Multiplicative Convolutions, Euler Products & Arithmetic Identities (12 modules)

- **Coprime kernel & Euler-product chain:** `ActualCoprimeConvolution`, `CoprimeKernelBounds`, `CoprimeKernelSummability`, `DivisorMomentBridge`, `CoprimeEulerMoment` — multiplicative kernel `g_d(n) = ψ(gcd(n,d))/ψ(n)`, `f(n)1_{(n,d)=1} = (μ * g_d)(n)`, `HasProd` convergence for `s > 1/2`, `τ(p^e)² ≤ d_4(p^e)`, and `< 2` local Euler-factor bounds at `s = 3/4` (`p = 2` with `r_2 = 2/3`).
- **Elementary & finite identities:** `MobiusHarmonicBound` (`|∑_{n≤N} μ(n)/n| ≤ 1`), `MobiusExponentialTail` (Laurent–exponential antiderivative and decay), `CoprimeFilterConvolution` (`r(d) ∈ (0, 1]`), `CoprimeMobiusFinite`, `CoprimeMobiusSigned` (`_root_.CommRing` signed-square identities isolating `Lean.Grind.CommRing`), `PublishedEnergyBridge` (`E_tail = E_trunc - 1`), and `VaughanIdentity` (`ArithmeticFunction ℝ`).

## 3. Mellin Multipliers, Stieltjes Tails & Integral Obstructions (12 modules)

- **Critical-strip Mellin, `ζ'/ζ`, & off-axis zeros:** `TentMultiplier`, `TentMellin`, `PrimePowerMellin`, `MellinZetaBridge`, `TentOperatorObstruction` — `mellin tent s ≠ 0` on `0 < Re(s) < 1`, sharp `Re(s) = 1/2` gap `√3 - 1 - 1/√2`, prime-power `-ζ'(s)/ζ(s)` identity on `1 < Re(s)`, and infinitely many zeros of `TentMultiplier.numerator` in `2 < Re(s) < 4`.
- **Logarithmic calibration:** `DensityCalibration`, `TentMoment`, `DensityMellin`, `FixedDensityMellin` — rational interval bounds for `log(4/3)` and `log 2` and calibrated mixture weights in `(0, 1)`.
- **Floor-kernel & Stieltjes tails:** `PowerKernelTransfer`, `StieltjesTailBridge` — floor-kernel remainder bound under `|G(t)| ≤ C t^(-γ)`, `80/89` minimax balance, finite Abel summation by parts, and `|G(t)| ≤ C (log t)^(-1-δ) ⇒ G(t)/t ∈ L¹([2, ∞))`.
- **Structural obstructions:** `ParityAndPickObstructions` — non-negativity of Selberg parity pseudo-densities `1 + t^(-1/4) cos(ω log t)`, Hardy model-space defect lower bound `(2 Re z - 1)/‖z‖² > 0`, and `2 × 2` principal-minor refutation of `Matrix.PosSemidef`.

## 4. Target Interfaces & Headline Index (2 modules)

- `MainTheorems` — single-entry export table with `#print axioms` checks for all 35 headline declarations.
- `TargetStatements` — Comparator-style frozen statement signatures paired with executable non-vacuity `example` witnesses verifying joint satisfiability of each theorem's hypotheses.
