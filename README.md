# 212-Mathematics (`RhAstraSynthesis`)

Lean 4 formalization (`leanprover/lean4:v4.34.0`, `mathlib@5ed2965256430c3649e86755f9576b54eca72435`) of polynomial extremal and Remez–Markov inequalities, coprime Möbius convolutions, and Mellin multiplier bounds, together with a Rocq `9.0` formalization of the finite rational signed-square envelope.

All 49 Lean submodules build without `sorry`, custom axioms, `native_decide`, or `Lean.ofReduceBool` under `lake build` and `leanchecker`, using only `[propext, Classical.choice, Quot.sound]`. Self-contained signatures and concrete examples live in [`TargetStatements.lean`](lean/RhAstraSynthesis/TargetStatements.lean); theorem dependencies and proofs are summarized in the [Blueprint PDF](blueprint/src/print.pdf) ([`content.tex`](blueprint/src/content.tex)).

## Headline Theorems

### 1. Polynomial Approximation, Bernstein & Markov–Remez Bounds

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Bernstein / Van der Corput–Schaake inequality | `bernsteinVanDerCorputSchaake` | $n^2 P(\cos\theta)^2 + (P'(\cos\theta)\sin\theta)^2 \le n^2 B^2$ ($\deg P \le n$) |
| Markov interior derivative inequality (1889) | `markovInteriorDerivative` | $\forall x \in [-1, 1],\; \lvert P'(x)\rvert \le n^2 B$ |
| Iterated interior Markov inequality | `markovIterateInteriorBound` | $\forall x \in [-1, 1],\; \lvert P^{(s)}(x)\rvert \le B \prod_{j < s}(n - j)^2$ |
| Interior interval transport | `markovInteriorIntervalTransfer` | $\lvert P^{(s)}(t)\rvert \le (2Lm)^s B \prod_{j < s}(m - j)^2$ on $[0, (Lm)^{-1}]$ |
| Exterior Chebyshev growth & endpoint Markov | `chebyshevExteriorBound`, `reciprocalEndpointMarkov` | $\lvert P(x)\rvert \le B\,T_m(\lvert x\rvert)$ ($\lvert x\rvert \ge 1$); $\lvert P^{(s)}(0)\rvert/s! \le M(4L)^s m^{3s}/(2s)!$ |
| Reciprocal-grid good-set measure | `reciprocalGoodMeasure` | $\lvert P(1/n)\rvert \le B \;(\forall n \ge 1) \implies \operatorname{meas}(\{t \in [0, 1/k] : \lvert P(t)\rvert \le B\}) \ge \frac{1}{k+m}$ |
| Remez–Chebyshev exponential envelope | `remezChebyshevEnvelope` | $T_m(2(Lm)^{-1}/e - 1) \le \exp(2m/\sqrt{L})$ |
| Measurable equioscillation Remez & Markov derivative | `remezInequality`, `remezExponentialInequality`, `remezMarkovInteriorBound` | $\lvert P(x)\rvert \le T_n(2(b-a)/\lvert E\rvert - 1) B$; $\lvert P^{(s)}(x)\rvert \le \bigl(\frac{2}{b-a}\bigr)^s \bigl(\prod_{j<s}(n-j)^2\bigr) T_n(2(b-a)/\lvert E\rvert-1) B$ |
| Affine Markov scaling & Gevrey factorial | `markovAffineTransfer`, `gevreyFactorialBound` | Factor $(2k)^s$ on $[0, 1/k]$; $(3k)!/(2k)! \le 8^k k!$ |
| Cubic sharpness witness on $\{1/n\}$ | `cubicSharpnessBound` | $\lvert P_{m,m}(1/n)\rvert \le 1$, $\deg P_{m,m} \le 2m$, $\lvert P_{m,m}'(0)\rvert \ge 2m^3 > m^2$ |
| Fractional $\{n^{-\alpha}\}$ envelope & $n^{-1/2}$ witness | `fractionalRemezEnvelope`, `sqrtSharpnessDerivative` | $T_m(2(Lm)^{-\alpha}/e - 1) \le \exp(2m\sqrt{\alpha/L})$; $\lvert Q_{m,m}'(0)\rvert \ge 2m^{5/2}$ |

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

The sampled series converges absolutely, and its remainder is identified with
the convergent series of polynomial remainders. Separately,
`polynomial_reciprocal_profiles_all_radii` proves absolute and uniform
convergence of each coefficient profile on closed subdisks, with bound
`|F_s(u)| ≤ (C/d)(64L/d³)^s s!`; `polynomial_reciprocal_profiles_holomorphic`
proves their holomorphy on the open disk. The explicit constant `1` is not
part of `F_0`: the full zeroth profile is `1 + F_0`.

These are reciprocal-sample results, not the open fractional-grid
Gevrey-alpha extension. No separate sampled-function holomorphy theorem or
mathematical originality/upstream acceptance claim is asserted here.
See the [proof dependency map](docs/RECIPROCAL_REMAINDER_GAP_MAP.md).

### 2. Multiplicative Convolutions, Euler Products & Arithmetic Identities

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Actual coprime Möbius factorization | `coprimeMobiusFactorization` | $f(n)\mathbf{1}_{(n,d)=1} = (\mu * g_d)(n)$, $g_d$ multiplicative |
| Infinite Euler product on $s > 1/2$ | `coprimeKernelEulerProduct` | $d \ne 0$, $s > 1/2 \implies \sum_{n \ge 1} g_d(n)n^{-s} = \prod_p \sum_k g_d(p^k)p^{-ks}$ |
| Modulus-uniform $s = 3/4$ local Euler bound | `coprimeEulerRatioBound` | $d \ne 0$, $p=2$ weight $r_2 = 2/3 \implies \prod_{p \mid d}(1 - r_p p^{-3/4})^{-1} \le \tau(d)$ |
| Uniform harmonic Möbius partial sums | `mobiusHarmonicBound` | $\forall N \ge 1,\; \lvert\sum_{n=1}^N \mu(n)/n\rvert \le 1$ |
| Laurent–exponential tail decay | `mobiusTailAntideriv`, `mobiusTailLogDecay` | Exact antiderivative of $z^3 e^{-cz}$ and $O_{c,A}(z^{-2A})$ bound |
| Vaughan, Baez–Duarte & signed-square identities | `vaughanIdentity`, `finiteEnergyExact`, `coprimeSignedSquare` | Dirichlet Vaughan split; $E_{\mathrm{tail}} = E_{\mathrm{trunc}} - 1$; `CommRing` identity |

### 3. Mellin Multipliers, Stieltjes Tails & Integral Obstructions

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Critical-strip tent Mellin non-vanishing | `tentMellinNonvanishing` | $0 < \operatorname{Re}(s) < 1 \implies \int_1^2 \tau(u)u^{s-1}\,\mathrm{d}u \ne 0$ |
| Prime-power Mellin–$\zeta'/\zeta$ identity | `primePowerMellinZeta` | $\operatorname{Re}(s) > 1$ dilated $-\zeta'(s)/\zeta(s)$ identity |
| Sharp critical-line tent gap | `tentHalfLineGap` | $\operatorname{Re}(s) = 1/2 \implies \lvert\mathrm{num}_\tau(s)\rvert \ge \sqrt{3} - 1 - 1/\sqrt{2} > 0$ |
| Non-outer off-axis tent zeros | `tentOffAxisZeros` | Infinitely many zeros of $\mathrm{num}_\tau$ in $2 < \operatorname{Re}(s) < 4$ |
| Floor-kernel $O(K^{-\gamma})$ transfer | `floorKernelErrorBound` | $\lvert G(t)\rvert \le C t^{-\gamma}$ ($0 < \gamma < 1$) Lebesgue error bound |
| Abel summation & polylogarithmic $L^1$ tails | `abelSummationInv`, `logDecayIntegrableTail` | $\lvert G(t)\rvert \le C(\log t)^{-1-\delta} \implies G(t)/t \in L^1([2,\infty))$ |
| Parity pseudo-density & Hardy/Pick obstructions | `parityPseudoDensityNonneg`, `modelSpaceDefectLowerBound`, `negMinorNotPosSemidef` | $1 + t^{-1/4}\cos(\omega\log t) \ge 0$; model-space defect $> 0$; $2\times 2$ minor refutation |

## Repository Layout

- [`lean/RhAstraSynthesis.lean`](lean/RhAstraSynthesis.lean) — Root module (`49` submodules).
- [`lean/RhAstraSynthesis/MainTheorems.lean`](lean/RhAstraSynthesis/MainTheorems.lean) — Theorem index with `#print axioms` checks.
- [`lean/RhAstraSynthesis/TargetStatements.lean`](lean/RhAstraSynthesis/TargetStatements.lean) — Self-contained theorem signatures and concrete examples.
- [`rocq/`](rocq/) — Rocq `9.0` finite rational signed-square envelope and sharpness counterexample (`rocqchk`).
- [`blueprint/src/content.tex`](blueprint/src/content.tex) — LaTeX blueprint linking theorems to Lean declarations ([PDF](blueprint/src/print.pdf)).
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — Module inventory.
- [`tests/`](tests/) — Numerical boundary checks (`test_mathematical_probes.py`) and repository consistency tests (`test_lean_integrity.py`).

## Verification

```bash
python3 -m unittest discover -s tests -p "test_*.py" -v
```

```bash
cd lean
lake exe cache get
lake build RhAstraSynthesis
lake env leanchecker RhAstraSynthesis
```

```bash
python3 rocq/verify_rocq.py   # requires Docker image rocq/rocq-prover:9.0
```
