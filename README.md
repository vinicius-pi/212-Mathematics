# 212-Mathematics (`Mathematics212`)

Lean 4 formalization (`leanprover/lean4:v4.34.0`, `mathlib@5ed2965256430c3649e86755f9576b54eca72435`) of polynomial extremal and Remez–Markov inequalities, reciprocal-grid Gevrey-1 expansions, and companion formalizations on coprime Möbius convolutions and tent Mellin multipliers, together with a separate Rocq `9.0` verification of a finite rational signed-square envelope. The central result follows the chain **reciprocal-grid good-set measure → measurable Remez → derivative bounds → coefficient profiles → reciprocal Gevrey-1 expansion**.

All 49 Lean submodules build without `sorry`, custom axioms, `native_decide`, or `Lean.ofReduceBool` under `lake build` and `leanchecker`, using only `[propext, Classical.choice, Quot.sound]`. Self-contained signatures and explicit examples live in [`TargetStatements.lean`](lean/Mathematics212/TargetStatements.lean); the reader-facing manuscript and archival blueprint live in the [Blueprint PDF](blueprint/src/print.pdf) ([`content.tex`](blueprint/src/content.tex)).

## Headline Theorems

### 1. Polynomial Approximation, Bernstein & Markov–Remez Bounds

| Mathematical Result | Lean Declaration (`Mathematics212.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Bernstein inequality (van der Corput–Schaake form) | `bernsteinVanDerCorputSchaake` | $n^2 P(\cos\theta)^2 + (P'(\cos\theta)\sin\theta)^2 \le n^2 B^2$ ($\deg P \le n$) |
| Markov interior derivative inequality (1889) | `markovInteriorDerivative` | $\forall x \in [-1, 1],\; \lvert P'(x)\rvert \le n^2 B$ |
| Iterated interior Markov inequality | `markovIterateInteriorBound` | $\forall x \in [-1, 1],\; \lvert P^{(s)}(x)\rvert \le B \prod_{j < s}(n - j)^2$ |
| Interior interval transport | `markovInteriorIntervalTransfer` | $\lvert P^{(s)}(t)\rvert \le (2Lm)^s B \prod_{j < s}(m - j)^2$ on $[0, (Lm)^{-1}]$ |
| Exterior Chebyshev growth & endpoint Markov | `chebyshevExteriorBound`, `reciprocalEndpointMarkov` | $\lvert P(x)\rvert \le B\,T_m(\lvert x\rvert)$ ($\lvert x\rvert \ge 1$); $\lvert P^{(s)}(0)\rvert/s! \le M(4L)^s m^{3s}/(2s)!$ |
| Reciprocal-grid good-set measure | `reciprocalGoodMeasure` | $\lvert P(1/n)\rvert \le B \;(\forall n \ge 1) \implies \mathrm{meas}(\{t \in [0, 1/k] : \lvert P(t)\rvert \le B\}) \ge \frac{1}{k+m}$ |
| Remez–Chebyshev exponential envelope | `remezChebyshevEnvelope` | $m \ge 1,\; L > 0,\; (Lm+m)^{-1} \le e \le (Lm)^{-1} \implies T_m(2(Lm)^{-1}/e - 1) \le \exp(2m/\sqrt{L})$ |
| Measurable equioscillation Remez & Markov derivative | `remezInequality`, `remezExponentialInequality`, `remezMarkovInteriorBound` | Borel $E \subseteq [a,b]$ (Lebesgue corollary via compact superset): $\lvert P(x)\rvert \le T_n(2(b-a)/\lvert E\rvert - 1) B$; $\lvert P^{(s)}(x)\rvert \le \bigl(\frac{2}{b-a}\bigr)^s \bigl(\prod_{j<s}(n-j)^2\bigr) T_n(2(b-a)/\lvert E\rvert-1) B$ |
| Affine Markov scaling & Gevrey factorial | `markovAffineTransfer`, `gevreyFactorialBound` | Factor $(2k)^s$ on $[0, 1/k]$; $(3k)!/(2k)! \le 8^k k!$ |
| Cubic witness against quadratic degree bounds on $\{1/n\}$ | `cubicSharpnessBound` | $\deg P_{m,m} \le 2m$, $\lvert P_{m,m}(1/n)\rvert \le 1$, $\lvert P_{m,m}'(0)\rvert \ge 2m^3$, ratio to $(2m)^2$ is $\ge m/2$ |
| Fractional $\{n^{-\alpha}\}$ envelope & $n^{-1/2}$ witness | `fractionalRemezEnvelope`, `sqrtSharpnessDerivative` | $m \ge 1,\; L > 0,\; 0 < \alpha \le 1,\; (Lm+m)^{-\alpha} \le e \le (Lm)^{-\alpha} \implies T_m(2(Lm)^{-\alpha}/e - 1) \le \exp(2m\sqrt{\alpha/L})$; $\deg Q_{m,m} \le 2m$, $\lvert Q_{m,m}'(0)\rvert \ge 2m^{5/2}$ |

### Reciprocal Gevrey-1 expansion

For real polynomials `P_m` with degree at most `m` and sample bounds
`|P_m(1/k)| ≤ C R^(-m)` for all positive `m,k`, where `C,R > 0`, define
`q_n(u) = 1 + ∑_{m≥1} P_m(1/n) u^m` and
`F_s(u) = ∑_{m≥1} ([X^s]P_m) u^m`.
The theorem `polynomial_reciprocal_gevrey_expansion` proves that for every
`0 ≤ r < R` there is one natural `L > 0`, chosen before all positive `n,p`
and all complex `u` with `|u| ≤ r`, such that, writing
`d = 1 - (r/R) exp(2/√L) > 0`,

```text
|q_n(u) - (1 + ∑_{s<p} F_s(u) n^(-s))|
  ≤ (3C/d) (72L/d³)^p p! / n^p.
```

The theorem `polynomial_reciprocal_gevrey_expansion` exports absolute
summability of the sampled series, the complex remainder identity, and the
norm inequality (while establishing absolute summability of the complex
remainder series internally as `hnorm`); `TargetStatements.reciprocal_gevrey_expansion`
projects the norm inequality alone. Separately, companion theorems
`polynomial_reciprocal_profiles_all_radii` and
`polynomial_reciprocal_profiles_holomorphic` establish absolute and uniform
convergence of each profile on closed subdisks (`|F_s(u)| ≤ (C/d)(64L/d³)^s s!`)
and holomorphy on the open disk `|u| < R`. The explicit constant `1` is not
part of `F_0`: the full zeroth profile is `1 + F_0`, and the expansion in
`1/n` is asymptotic as `n → ∞` for fixed `p`.

See the [proof dependency map](docs/RECIPROCAL_GEVREY_PROOF.md).

### 2. Companion Part I: Multiplicative Convolutions, Euler Products & Arithmetic Identities

| Mathematical Result | Lean Declaration (`Mathematics212.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Actual coprime Möbius factorization | `coprimeMobiusFactorization` | $f(n)\mathbf{1}_{(n,d)=1} = (\mu * g_d)(n)$, $g_d$ divisor-sum defined, multiplicative |
| Infinite Euler product on $s > 1/2$ | `coprimeKernelEulerProduct` | $d \ne 0$, real $s > 1/2 \implies \sum_{n \ge 1} g_d(n)n^{-s} = \prod_p \sum_k g_d(p^k)p^{-ks}$ |
| Modulus-uniform $s = 3/4$ local Euler bound | `coprimeEulerRatioBound` | $d \ne 0$, $r_p = p/(p+1)$ ($r_2 = 2/3$) $\implies \prod_{p \mid d}(1 - r_p p^{-3/4})^{-1} \le \tau(d)$ |
| Uniform harmonic Möbius partial sums | `mobiusHarmonicBound` | $\forall N \ge 1,\; \lvert\sum_{n=1}^N \mu(n)/n\rvert \le 1$ |
| Laurent–exponential tail decay | `mobiusTailAntideriv`, `mobiusTailLogDecay` | Derivative gives $-2z^3 e^{-cz}$; for integer $A \ge 0$, $z^3 e^{-cz} = O_{c,A}(z^{-2A})$ on $z \ge 1$ |
| Vaughan, Baez–Duarte & signed-square identities | `vaughanIdentity`, `finiteEnergyExact`, `coprimeSignedSquare` | Dirichlet Vaughan split; finite sum $E_{\mathrm{tail}} = E_{\mathrm{trunc}} - 1$ ($u,Y \ge 1$); `CommRing` identity |

### 3. Companion Part II: Mellin Multipliers, Stieltjes Tails & Conditional Obstructions

| Mathematical Result | Lean Declaration (`Mathematics212.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Critical-strip tent Mellin non-vanishing | `tentMellinNonvanishing` | $0 < \mathrm{Re}(s) < 1 \implies \int_1^2 \tau(u)u^{s-1}\,\mathrm{d}u \ne 0$ ($\tau$ piecewise affine in $1/u$) |
| Prime-power Mellin–$\zeta'/\zeta$ identity | `primePowerMellinZeta` | $\mathrm{Re}(s) > 1$: Mellin transform of `primePower` at $-s$ equals $M_\tau(s)(-\zeta'(s)/\zeta(s))$ |
| Sharp critical-line tent gap | `tentHalfLineGap` | $\mathrm{Re}(s) = 1/2 \implies \lvert\mathrm{num}_\tau(s)\rvert \ge \sqrt{3} - 1 - 1/\sqrt{2} > 0$ (equality at $s = 1/2$) |
| Off-axis zeros of tent numerator | `tentOffAxisZeros` | $\forall H > 0,\; \exists s$ with $2 < \mathrm{Re}(s) < 4$, $\mathrm{Im}(s) > H$, $\mathrm{num}_\tau(s) = 0$ |
| Floor-kernel $O(K^{-\gamma})$ transfer | `floorKernelErrorBound` | $\lvert G(t)\rvert \le C t^{-\gamma}$ ($t \ge 1$, $0 < \gamma < 1$) $\implies$ error $\le C(1/\gamma + 1/(1-\gamma))K^{-\gamma}$ ($K \ge 1$) |
| Abel summation & polylogarithmic $L^1$ tails | `abelSummationInv`, `logDecayIntegrableTail` | $1 \le u \le N$; $\lvert G(t)\rvert \le C(\log t)^{-1-\delta}$ ($t \ge 2$) $\implies G(t)/t \in L^1((K,\infty))$ ($K \ge 2$) |
| Parity pseudo-density, conditional Hilbert defect & $2\times 2$ minor test | `parityPseudoDensityNonneg`, `modelSpaceDefectLowerBound`, `negMinorNotPosSemidef` | $1 + t^{-1/4}\cos(\omega\log t) \ge 0$; conditional Hilbert-space defect $\ge (2\,\mathrm{Re}\,z - 1)/\lVert z\rVert^2 > 0$; negative $2\times 2$ minor refutes `Matrix.PosSemidef` |

## Repository Layout

- [`lean/Mathematics212.lean`](lean/Mathematics212.lean) — Root module (`49` submodules).
- [`lean/Mathematics212/MainTheorems.lean`](lean/Mathematics212/MainTheorems.lean) — Theorem index with `#print axioms` checks.
- [`lean/Mathematics212/TargetStatements.lean`](lean/Mathematics212/TargetStatements.lean) — Self-contained theorem signatures and explicit examples.
- [`rocq/`](rocq/) — Rocq `9.0` finite rational signed-square envelope and sharpness counterexample (`rocqchk`; does not cross-check the Lean analysis).
- [`blueprint/src/content.tex`](blueprint/src/content.tex) — Reader-facing manuscript and LaTeX blueprint linking theorems to Lean declarations ([PDF](blueprint/src/print.pdf)).
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — Module inventory.
- [`tests/`](tests/) — Numerical boundary checks (`test_mathematical_probes.py`) and repository consistency tests (`test_lean_integrity.py`).

## Verification

```bash
python3 -m unittest discover -s tests -p "test_*.py" -v
```

```bash
cd lean
lake exe cache get
lake build Mathematics212
lake env leanchecker Mathematics212
```

```bash
python3 rocq/verify_rocq.py   # requires Docker image rocq/rocq-prover:9.0
```

## Author, Provenance & Scope

**Author:** Vinícius Marques Pimenta

AI tools assisted with portions of the Lean 4 and Rocq 9.0 formalizations, tests, and exposition. Lean checks the formal declarations (`lake build`, `leanchecker`), Rocq independently checks the finite rational envelope (`rocqchk`), and Python checks the test suite. These mechanical checks do not certify the correspondence between the manuscript prose and the formal statements, nor do they replace independent mathematical peer review.
