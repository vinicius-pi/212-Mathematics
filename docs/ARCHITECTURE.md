# Architecture & Module Inventory

`Mathematics212` (`leanprover/lean4:v4.34.0`, `mathlib@5ed2965256430c3649e86755f9576b54eca72435`) imports 49 submodules in four groups (23, 12, 12, and 2), as enumerated in [`Mathematics212.lean`](../lean/Mathematics212.lean), and is indexed through [`MainTheorems.lean`](../lean/Mathematics212/MainTheorems.lean) and [`TargetStatements.lean`](../lean/Mathematics212/TargetStatements.lean).

## 1. Polynomial Approximation, Bernstein & Markov–Remez Bounds (23 modules)

- **Reciprocal-grid measure reduction:** `ReciprocalGap`, `ReciprocalMeasure`, `ReciprocalGapOrder`, `OccupiedGap`, `ReciprocalGapSum`, `PolynomialReciprocalMeasure` — Rolle-based bad-gap counting and Lebesgue measure bound `|E| ≥ 1/(k + m)` on `[0, 1/k]`.
- **Measurable Remez inequality & exponential envelope:** `RemezNormalization`, `ChebyshevExponentialEnvelope`, `RemezInequality` — `remez_argument_of_measure`, `remez_chebyshev_T_le_exp` (`T_m(1 + 2/L) ≤ exp(2m/√L)` for `m ≥ 1`, `L > 0`, `(Lm + m)⁻¹ ≤ e ≤ (Lm)⁻¹`), Borel Remez bound `|P(x)| ≤ T_n(2(b-a)/|E| - 1) B` via Bojanov's cumulative-measure interpolation nodes and compact good superset `K = [a, b] ∩ {|P| ≤ B}` (extending as a paper corollary to Lebesgue-measurable sets), exponential Remez corollary `|P(x)| ≤ exp(2n/√L) B`, and combined Remez + iterated Markov interior derivative bound `|P^(s)(x)| ≤ (2/(b-a))^s (∏_{j<s} (n-j)^2) T_n(2(b-a)/|E| - 1) B`.
- **Bernstein, interior Markov & Gevrey scalings:** `MarkovAlgebraicFactors`, `MarkovFactorialNormalization`, `GevreyMomentFactorial`, `MarkovAffineTransport`, `MarkovChebyshevEndpoint`, `MarkovChebyshevGeneral`, `MarkovInterior` — affine derivative chain rule, endpoint Markov saturation at `±1`, scaled exterior bound `|P(x)| ≤ B T_m(|x|)` (`|x| ≥ 1`), Bernstein inequality (in the form treated by van der Corput and Schaake) `n² P(cos θ)² + (P'(cos θ) sin θ)² ≤ n² B²`, A. A. Markov's 1889 interior bound `|P'(x)| ≤ n² B` on `[-1, 1]` with `s`-fold iteration `∏_{j < s} (n - j)² B`, unconditional endpoint and interior transports to `[0, 1/(Lm)]`, and `(3k)!/(2k)! ≤ 8^k k!`.
- **Fractional-grid analysis & sharpness witnesses:** `ReciprocalSharpnessWitness`, `FractionalGridBounds` — `{1/n}` cubic witness (`deg P_{m,m} ≤ 2m`, `|P_{m,m}'(0)| ≥ 2m³ > (2m)²` for large `m`), `{n^(-α)}` gap monotonicity and telescoping, fractional Remez–Chebyshev envelope `T_m(2(Lm)^(-α)/e - 1) ≤ exp(2m√(α/L))` for `m ≥ 1`, `L > 0`, `0 < α ≤ 1`, `(Lm + m)^(-α) ≤ e ≤ (Lm)^(-α)`, and `1/√n` witness (`deg Q_{m,m} ≤ 2m`, `|Q_{m,m}'(0)| ≥ 2m^(5/2)`).

### Reciprocal coefficient profiles and full remainder

The five modules below form the reciprocal Gevrey-1 proof chain.

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
  `polynomial_reciprocal_gevrey_expansion` exports sampled summability,
  the complex remainder identity, and the norm estimate (proving complex
  remainder summability internally as `hnorm`); `TargetStatements.reciprocal_gevrey_expansion`
  projects only the norm estimate, and `polynomial_reciprocal_profiles_holomorphic`
  is a separate companion theorem.

See the [dependency map](RECIPROCAL_GEVREY_PROOF.md) for exact declarations.

## 2. Companion Part I: Multiplicative Convolutions, Euler Products & Arithmetic Identities (12 modules)

- **Coprime kernel & Euler-product chain:** `ActualCoprimeConvolution`, `CoprimeKernelBounds`, `CoprimeKernelSummability`, `DivisorMomentBridge`, `CoprimeEulerMoment` — divisor-sum kernel `g_d(n) = ∑_{a ∣ n, (a,d)=1} f(a)` (with multiplicative prime-product form `actual_coprime_kernel_eq_prime_product` equal to `ψ(gcd(n,d))/ψ(n)` for `n ≥ 1`), `f(n)1_{(n,d)=1} = (μ * g_d)(n)`, `HasProd` convergence for real `s > 1/2` and `d ≠ 0`, `τ(p^e)² ≤ d_4(p^e)`, and `< 2` local Euler-factor bounds at `s = 3/4` (`r_p = p/(p+1)`, `r_2 = 2/3`).
- **Elementary & finite identities:** `MobiusHarmonicBound` (`|∑_{n≤N} μ(n)/n| ≤ 1`), `MobiusExponentialTail` (antiderivative of `-2z³ e^(-cz)` and `O_{c,A}(z^(-2A))` decay for integer `A ≥ 0`, `z ≥ 1`), `CoprimeFilterConvolution` (`r(d) ∈ (0, 1]`), `CoprimeMobiusFinite`, `CoprimeMobiusSigned` (`_root_.CommRing` signed-square identities isolating `Lean.Grind.CommRing`), `PublishedEnergyBridge` (finite integer sum-of-squares identity `E_tail = E_trunc - 1` for `u, Y ≥ 1`), and `VaughanIdentity` (`ArithmeticFunction ℝ`).

## 3. Companion Part II: Mellin Multipliers, Stieltjes Tails & Conditional Obstructions (12 modules)

- **Critical-strip Mellin, `ζ'/ζ`, & off-axis zeros:** `TentMultiplier`, `TentMellin`, `PrimePowerMellin`, `MellinZetaBridge`, `TentOperatorObstruction` — `mellin tent s ≠ 0` on `0 < Re(s) < 1` (for the piecewise-affine-in-`1/u` tent `τ`), sharp `Re(s) = 1/2` gap `√3 - 1 - 1/√2` (equality at `s = 1/2`), `primePower` Mellin transform at `-s` matching `mellin tent s * (-ζ'(s)/ζ(s))` on `1 < Re(s)` (no critical-strip continuation asserted), and zeros of `TentMultiplier.numerator` in `2 < Re(s) < 4` above every height cutoff `H` via good-index phase selection and ball self-map contraction.
- **Logarithmic calibration:** `DensityCalibration`, `TentMoment`, `DensityMellin`, `FixedDensityMellin` — rational interval bounds for `log(4/3)` and `log 2` and calibrated mixture weights in `(0, 1)`.
- **Floor-kernel & Stieltjes tails:** `PowerKernelTransfer`, `StieltjesTailBridge` — floor-kernel remainder bound `C(1/γ + 1/(1-γ)) K^(-γ)` (`K ≥ 1`) under `|G(t)| ≤ C t^(-γ)` (`t ≥ 1`), separate exponent-balance inequality `(80/89) ≤ max((3+a)/4, (26-18a)/17)` (`exponent_envelope`), finite Abel summation by parts (`1 ≤ u ≤ N`), and `|G(t)| ≤ C (log t)^(-1-δ) ⇒ G(t)/t ∈ L¹((K, ∞))` (`K ≥ 2`).
- **Conditional obstructions:** `ParityAndPickObstructions` — non-negativity of Selberg parity pseudo-densities `1 + t^(-1/4) cos(ω log t)` (`t ≥ 1`), conditional Hilbert-space defect lower bound `(2 Re z - 1)/‖z‖² > 0` under unit-vector orthogonality and pairing hypotheses, and `2 × 2` principal-minor refutation of `Matrix.PosSemidef` (without constructing a concrete Hardy subspace or theta-deformation minor).

## 4. Target Interfaces & Headline Index (2 modules)

- `MainTheorems` — single-entry export table with 41 aliases and `#print axioms` checks.
- `TargetStatements` — self-contained Mathlib-type theorem signatures paired with explicit examples checking that their hypotheses hold simultaneously.
