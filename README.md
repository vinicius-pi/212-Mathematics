# RhAstraSynthesis

Machine-checked Lean 4 formalizations (`leanprover/lean4:v4.34.0`, Mathlib) in polynomial approximation, coprime Möbius convolutions, Mellin multipliers for $-\zeta'/\zeta$, and analytic obstructions. All 32 headline theorems in [`RhAstraSynthesis.MainTheorems`](lean/RhAstraSynthesis/MainTheorems.lean) depend exclusively on the standard Lean axioms `[propext, Classical.choice, Quot.sound]`, checked with zero `sorry` across all 42 submodules via `lake build` and `leanchecker`.

The mathematical dependency graph and proof sketches are compiled in the [Blueprint PDF](blueprint/src/print.pdf) (`blueprint/src/content.tex`).

## Headline Theorems

### 1. Markov–Chebyshev Inequalities, Bernstein Bounds & Reciprocal-Grid Approximation

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Bernstein / Van der Corput–Schaake inequality | `bernsteinVanDerCorputSchaake` | $n^2 P(\cos\theta)^2 + (P'(\cos\theta)\sin\theta)^2 \le n^2 B^2$ ($\deg P \le n$) |
| Markov interior derivative inequality (1889) | `markovInteriorDerivative` | $\forall x \in [-1, 1],\; \|P'(x)\| \le n^2 B$ |
| Iterated interior Markov inequality | `markovIterateInteriorBound` | $\forall x \in [-1, 1],\; \|P^{(s)}(x)\| \le B \prod_{j < s}(n - j)^2$ |
| Interior interval transport | `markovInteriorIntervalTransfer` | $\|P^{(s)}(t)\| \le (2Lm)^s B \prod_{j < s}(m - j)^2$ on $[0, (Lm)^{-1}]$ |
| Exterior Chebyshev growth & endpoint Markov | `chebyshevExteriorBound`, `reciprocalEndpointMarkov` | $\|P(x)\| \le B\,T_m(\|x\|)$ ($\|x\| \ge 1$); $\|P^{(s)}(0)\|/s! \le M(4L)^s m^{3s}/(2s)!$ |
| Reciprocal-grid good-set measure | `reciprocalGoodMeasure` | $\|P(1/n)\| \le B \;(\forall n \ge 1) \implies \|\{t \in [0, 1/k] : \|P(t)\| \le B\}\| \ge \frac{1}{k+m}$ |
| Remez–Chebyshev exponential envelope | `remezChebyshevEnvelope` | $T_m(2(Lm)^{-1}/e - 1) \le \exp(2m/\sqrt{L})$ |
| Affine Markov scaling & Gevrey factorial | `markovAffineTransfer`, `gevreyFactorialBound` | Factor $(2k)^s$ on $[0, 1/k]$; $(3k)!/(2k)! \le 8^k k!$ |
| Cubic sharpness witness on $\{1/n\}$ | `cubicSharpnessBound` | $\|P_{m,m}(1/n)\| \le 1$, $\deg P_{m,m} \le 2m$, $\|P_{m,m}'(0)\| \ge 2m^3 > m^2$ |
| Fractional $\{n^{-\alpha}\}$ Remez envelope & $n^{-1/2}$ witness | `fractionalRemezEnvelope`, `sqrtSharpnessDerivative` | $T_m(2(Lm)^{-\alpha}/e - 1) \le \exp(2m\sqrt{\alpha/L})$; $\|Q_{m,m}'(0)\| \ge 2m^{5/2}$ |

### 2. Coprime Möbius Convolutions, Euler Products & Arithmetic Identities

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Actual coprime Möbius factorization | `coprimeMobiusFactorization` | $f(n)\mathbf{1}_{(n,d)=1} = (\mu * g_d)(n)$, $g_d$ multiplicative |
| Infinite Euler product on $s > 1/2$ | `coprimeKernelEulerProduct` | $d \ne 0$, $s > 1/2 \implies \sum_{n \ge 1} g_d(n)n^{-s} = \prod_p \sum_k g_d(p^k)p^{-ks}$ |
| Modulus-uniform $s = 3/4$ local Euler bound | `coprimeEulerRatioBound` | $d \ne 0$, $p=2$ weight $r_2 = 2/3 \implies \prod_{p \mid d}(1 - r_p p^{-3/4})^{-1} \le \tau(d)$ |
| Uniform harmonic Möbius partial sums | `mobiusHarmonicBound` | $\forall N \ge 1,\; \|\sum_{n=1}^N \mu(n)/n\| \le 1$ |
| Laurent–exponential tail decay | `mobiusTailAntideriv`, `mobiusTailLogDecay` | Exact antiderivative of $z^3 e^{-cz}$ and $O_{c,A}(z^{-2A})$ bound |
| Vaughan, Baez–Duarte & signed-square identities | `vaughanIdentity`, `finiteEnergyExact`, `coprimeSignedSquare` | Dirichlet Vaughan split; $E_{\mathrm{tail}} = E_{\mathrm{trunc}} - 1$; `CommRing` identity |

### 3. Mellin Multipliers, Stieltjes Tails & Integral Obstructions

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Core Hypothesis / Bound |
| :--- | :--- | :--- |
| Critical-strip tent Mellin non-vanishing | `tentMellinNonvanishing` | $0 < \operatorname{Re}(s) < 1 \implies \int_1^2 \tau(u)u^{s-1}\,\mathrm{d}u \ne 0$ |
| Prime-power Mellin–$\zeta'/\zeta$ identity | `primePowerMellinZeta` | $\operatorname{Re}(s) > 1$ dilated $-\zeta'(s)/\zeta(s)$ identity |
| Sharp critical-line tent gap | `tentHalfLineGap` | $\operatorname{Re}(s) = 1/2 \implies \|\mathrm{num}_\tau(s)\| \ge \sqrt{3} - 1 - 1/\sqrt{2} > 0$ |
| Non-outer off-axis tent zeros | `tentOffAxisZeros` | Infinitely many zeros of $\mathrm{num}_\tau$ in $2 < \operatorname{Re}(s) < 4$ |
| Floor-kernel $O(K^{-\gamma})$ transfer | `floorKernelErrorBound` | $\|G(t)\| \le C t^{-\gamma}$ ($0 < \gamma < 1$) Lebesgue error bound |
| Abel summation & polylogarithmic $L^1$ tails | `abelSummationInv`, `logDecayIntegrableTail` | $\|G(t)\| \le C(\log t)^{-1-\delta} \implies G(t)/t \in L^1([2,\infty))$ |
| Parity pseudo-density & Hardy/Pick obstructions | `parityPseudoDensityNonneg`, `modelSpaceDefectLowerBound`, `negMinorNotPosSemidef` | $1 + t^{-1/4}\cos(\omega\log t) \ge 0$; model-space defect $> 0$; $2\times 2$ minor refutation |

## Repository Structure

- [`lean/RhAstraSynthesis.lean`](lean/RhAstraSynthesis.lean) — Root module aggregating all 42 Lean 4 submodules.
- [`lean/RhAstraSynthesis/`](lean/RhAstraSynthesis/) — Formalized modules ([architecture inventory](docs/ARCHITECTURE.md)).
- [`blueprint/src/content.tex`](blueprint/src/content.tex) — LaTeX blueprint (`definition`/`lemma`/`theorem`/`proof` dependency graph) compiled to [`blueprint/src/print.pdf`](blueprint/src/print.pdf).
- [`tests/test_mathematical_probes.py`](tests/test_mathematical_probes.py) — Exact rational and precision probes testing boundary conditions and extremal witnesses.
- [`.github/workflows/verify.yml`](.github/workflows/verify.yml) — CI pipeline running `lake build`, `leanchecker`, zero-`sorry` audit, and Python probes.

## Verification

```bash
cd lean
lake build RhAstraSynthesis
lake env leanchecker RhAstraSynthesis
```

```bash
python -m unittest discover -s tests -p "test_*.py" -v
```
