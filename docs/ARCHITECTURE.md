# Architecture & Module Inventory

`RhAstraSynthesis` (`leanprover/lean4:v4.34.0`, `mathlib@5ed2965256430c3649e86755f9576b54eca72435`) imports 49 submodules in four groups (23, 12, 12, and 2), as enumerated in [`RhAstraSynthesis.lean`](../lean/RhAstraSynthesis.lean), and is indexed through [`MainTheorems.lean`](../lean/RhAstraSynthesis/MainTheorems.lean) and [`TargetStatements.lean`](../lean/RhAstraSynthesis/TargetStatements.lean).

## 1. Polynomial Approximation, Bernstein & Markov–Remez Bounds (23 modules)

- **Reciprocal-grid measure reduction:** `ReciprocalGap`, `ReciprocalMeasure`, `ReciprocalGapOrder`, `OccupiedGap`, `ReciprocalGapSum`, `PolynomialReciprocalMeasure` — Rolle-based bad-gap counting and Lebesgue measure bound `|E| ≥ 1/(k + m)` on `[0, 1/k]`.
- **Measurable Remez inequality & exponential envelope:** `RemezNormalization`, `ChebyshevExponentialEnvelope`, `RemezInequality` — `remez_argument_of_measure`, `remez_chebyshev_T_le_exp` (`T_m(1 + 2/L) ≤ exp(2m/√L)`), full measurable equioscillation Remez bound `|P(x)| ≤ T_n(2(b-a)/|E| - 1) B` via Bojanov's Lagrange–Chebyshev node-selection proof, exponential Remez corollary `|P(x)| ≤ exp(2n/√L) B`, and combined Remez + iterated Markov interior derivative bound `|P^(s)(x)| ≤ (2/(b-a))^s (∏_{j<s} (n-j)^2) T_n(2(b-a)/|E| - 1) B`.
- **Bernstein, interior Markov & Gevrey scalings:** `MarkovAlgebraicFactors`, `MarkovFactorialNormalization`, `GevreyMomentFactorial`, `MarkovAffineTransport`, `MarkovChebyshevEndpoint`, `MarkovChebyshevGeneral`, `MarkovInterior` — affine derivative chain rule, endpoint Markov saturation at `±1`, scaled exterior bound `|P(x)| ≤ B T_m(|x|)` (`|x| ≥ 1`), Bernstein / Van der Corput–Schaake inequality `n² P(cos θ)² + (P'(cos θ) sin θ)² ≤ n² B²`, A. A. Markov's 1889 interior bound `|P'(x)| ≤ n² B` on `[-1, 1]` with `s`-fold iteration `∏_{j < s} (n - j)² B`, unconditional endpoint and interior transports to `[0, 1/(Lm)]`, and `(3k)!/(2k)! ≤ 8^k k!`.
- **Fractional-grid analysis & sharpness witnesses:** `ReciprocalSharpnessWitness`, `FractionalGridBounds` — `{1/n}` cubic witness `|P_{m,m}'(0)| ≥ 2m³ > m²`, `{n^(-α)}` gap monotonicity and telescoping, Bernoulli–Chebyshev envelope `exp(2m√(α/L))`, and `1/√n` witness `|Q_{m,m}'(0)| ≥ 2m^(5/2) > m²`.

### Reciprocal coefficient profiles and full remainder

The five modules below complete the reciprocal Gevrey-1 chain; they do not
establish the fractional-grid Gevrey-alpha proposition.

- `ReciprocalGevreyMajorant` — positive-index geometric and mixed moments,
  cubic factorial majorant, sample-derived family coefficient bounds, and
  `exists_reciprocal_gevrey_parameter`: one natural parameter for every order
  at each strict subradius, including radius zero.
- `ReciprocalCoefficientProfile` — normalized derivative series identified
  with polynomial coefficients; absolute and uniform convergence on closed
  subdisks (`polynomial_reciprocal_profiles_all_radii`) and open-disk
  holomorphy (`polynomial_reciprocal_profiles_holomorphic`).
- `ReciprocalTaylorRemainder` — coefficient/Taylor identification, finite
  Lagrange remainder for `Lm ≤ n`, exact vanishing above degree, and the
  complementary `n ≤ Lm` estimate retaining `m^(p+2s)/(2s)!`.
- `ReciprocalRemainderSeries` — `polynomial_reciprocal_family_remainder_gevrey`
  proves summability of the absolute real weighted remainder and bounds it by
  `(3C/d)(72L/d³)^p p!/n^p`, where `d=1-(r/R)exp(2/√L)>0`.
  A global sum of positive majorants avoids an infinite indicator partition.
- `ReciprocalGevreyExpansion` — sampled complex series with explicit constant
  `1`, finite profile expansion, absolute sampled convergence, justified
  finite-sum/series interchange, and `polynomial_reciprocal_gevrey_expansion`.
  Under `deg P_m ≤ m` and `|P_m(1/k)| ≤ C R^(-m)` for positive `m,k`,
  every `0 ≤ r < R` admits one `L` for the preceding bound, simultaneously
  for positive `n,p` and `|u| ≤ r`. The full zeroth profile is `1+F_0`.

Only coefficient-profile holomorphy has a dedicated theorem here; the
sampled-function interface states convergence and remainder control.
See the [dependency map](RECIPROCAL_REMAINDER_GAP_MAP.md) for exact declarations.

## 2. Multiplicative Convolutions, Euler Products & Arithmetic Identities (12 modules)

- **Coprime kernel & Euler-product chain:** `ActualCoprimeConvolution`, `CoprimeKernelBounds`, `CoprimeKernelSummability`, `DivisorMomentBridge`, `CoprimeEulerMoment` — multiplicative kernel `g_d(n) = ψ(gcd(n,d))/ψ(n)`, `f(n)1_{(n,d)=1} = (μ * g_d)(n)`, `HasProd` convergence for `s > 1/2`, `τ(p^e)² ≤ d_4(p^e)`, and `< 2` local Euler-factor bounds at `s = 3/4` (`p = 2` with `r_2 = 2/3`).
- **Elementary & finite identities:** `MobiusHarmonicBound` (`|∑_{n≤N} μ(n)/n| ≤ 1`), `MobiusExponentialTail` (Laurent–exponential antiderivative and decay), `CoprimeFilterConvolution` (`r(d) ∈ (0, 1]`), `CoprimeMobiusFinite`, `CoprimeMobiusSigned` (`_root_.CommRing` signed-square identities isolating `Lean.Grind.CommRing`), `PublishedEnergyBridge` (`E_tail = E_trunc - 1`), and `VaughanIdentity` (`ArithmeticFunction ℝ`).

## 3. Mellin Multipliers, Stieltjes Tails & Integral Obstructions (12 modules)

- **Critical-strip Mellin, `ζ'/ζ`, & off-axis zeros:** `TentMultiplier`, `TentMellin`, `PrimePowerMellin`, `MellinZetaBridge`, `TentOperatorObstruction` — `mellin tent s ≠ 0` on `0 < Re(s) < 1`, sharp `Re(s) = 1/2` gap `√3 - 1 - 1/√2`, prime-power `-ζ'(s)/ζ(s)` identity on `1 < Re(s)`, and infinitely many zeros of `TentMultiplier.numerator` in `2 < Re(s) < 4`.
- **Logarithmic calibration:** `DensityCalibration`, `TentMoment`, `DensityMellin`, `FixedDensityMellin` — rational interval bounds for `log(4/3)` and `log 2` and calibrated mixture weights in `(0, 1)`.
- **Floor-kernel & Stieltjes tails:** `PowerKernelTransfer`, `StieltjesTailBridge` — floor-kernel remainder bound under `|G(t)| ≤ C t^(-γ)`, `80/89` minimax balance, finite Abel summation by parts, and `|G(t)| ≤ C (log t)^(-1-δ) ⇒ G(t)/t ∈ L¹([2, ∞))`.
- **Structural obstructions:** `ParityAndPickObstructions` — non-negativity of Selberg parity pseudo-densities `1 + t^(-1/4) cos(ω log t)`, Hardy model-space defect lower bound `(2 Re z - 1)/‖z‖² > 0`, and `2 × 2` principal-minor refutation of `Matrix.PosSemidef`.

## 4. Target Interfaces & Headline Index (2 modules)

- `MainTheorems` — single-entry export table with 41 aliases and `#print axioms` checks.
- `TargetStatements` — self-contained Mathlib-type theorem signatures paired with concrete instantiations checking that their hypotheses hold simultaneously.
