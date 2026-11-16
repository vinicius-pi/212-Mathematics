# 212-Mathematics (`RhAstraSynthesis`)

Machine-verified Lean 4 formalizations (`leanprover/lean4:v4.34.0`, pinned `mathlib@5ed2965256430c3649e86755f9576b54eca72435`) across extremal polynomial approximation, coprime Möbius convolutions, Mellin multipliers for $-\zeta'/\zeta$, and analytic obstructions, accompanied by a Rocq `9.0` finite-rational cross-check.

All 43 Lean submodules build with zero `sorry` under `lake build` and `leanchecker`, depend solely on the standard kernel axioms `[propext, Classical.choice, Quot.sound]`, ban `native_decide` and `Lean.ofReduceBool`, and include executable non-vacuity witnesses in [`TargetStatements.lean`](lean/RhAstraSynthesis/TargetStatements.lean).

## Scope and Non-Claims

1. **No RH or Quasi-RH proof.** Nothing here proves the Riemann Hypothesis, any zero-free half-plane $\operatorname{Re}(s) > \sigma_0$ with $\sigma_0 < 1$, or a global $L^1(\mathrm{d}x/x)$ bound on the signed prime-sum remainder.
2. **Closed versus open approximation bounds.** A. A. Markov's interior derivative inequality (`[-1, 1]`), Bernstein / Van der Corput–Schaake, exterior Chebyshev growth, and reciprocal/fractional-grid Remez envelopes are formalized; the classical Remez equioscillation inequality on arbitrary measurable subsets $E \subseteq I$ remains open (`\notready` in [`blueprint/src/content.tex`](blueprint/src/content.tex)).
3. **Closed versus open arithmetic inputs.** Coprime factorization, $s > 1/2$ Euler-product convergence (`HasProd`), local $s = 3/4$ Euler bounds ($< 2$), and polylogarithmic Stieltjes $L^1$ tail bounds are formalized; unconditional Prime Number Theorem and Vinogradov–Korobov inputs remain external hypotheses.

## Headline Theorems

### 1. Polynomial Approximation, Bernstein & Markov–Remez Bounds

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Verified Bound / Statement |
| :--- | :--- | :--- |
| Bernstein / Van der Corput–Schaake | `bernsteinVanDerCorputSchaake` | $n^2 P(\cos\theta)^2 + (P'(\cos\theta)\sin\theta)^2 \le n^2 B^2$ ($\deg P \le n$) |
| Markov interior derivative (1889) | `markovInteriorDerivative` | $\forall x \in [-1, 1],\; \|P'(x)\| \le n^2 B$ |
| Iterated interior Markov | `markovIterateInteriorBound` | $\forall x \in [-1, 1],\; \|P^{(s)}(x)\| \le B \prod_{j < s}(n - j)^2$ |
| Interior interval transport | `markovInteriorIntervalTransfer` | $\|P^{(s)}(t)\| \le (2Lm)^s B \prod_{j < s}(m - j)^2$ on $[0, (Lm)^{-1}]$ |
| Exterior growth & endpoint Markov | `chebyshevExteriorBound`, `reciprocalEndpointMarkov` | $\|P(x)\| \le B\,T_m(\|x\|)$ ($\|x\| \ge 1$); $\|P^{(s)}(0)\|/s! \le M(4L)^s m^{3s}/(2s)!$ |
| Reciprocal-grid good-set measure | `reciprocalGoodMeasure` | $\|P(1/n)\| \le B \;(\forall n \ge 1) \implies \|\{t \in [0, 1/k] : \|P(t)\| \le B\}\| \ge \frac{1}{k+m}$ |
| Remez–Chebyshev exponential envelope | `remezChebyshevEnvelope` | $T_m(2(Lm)^{-1}/e - 1) \le \exp(2m/\sqrt{L})$ |
| Affine Markov & Gevrey factorial | `markovAffineTransfer`, `gevreyFactorialBound` | Factor $(2k)^s$ on $[0, 1/k]$; $(3k)!/(2k)! \le 8^k k!$ |
| Cubic sharpness witness on $\{1/n\}$ | `cubicSharpnessBound` | $\|P_{m,m}(1/n)\| \le 1$, $\deg P_{m,m} \le 2m$, $\|P_{m,m}'(0)\| \ge 2m^3 > m^2$ |
| Fractional $\{n^{-\alpha}\}$ envelope & $n^{-1/2}$ witness | `fractionalRemezEnvelope`, `sqrtSharpnessDerivative` | $T_m(2(Lm)^{-\alpha}/e - 1) \le \exp(2m\sqrt{\alpha/L})$; $\|Q_{m,m}'(0)\| \ge 2m^{5/2}$ |

### 2. Multiplicative Convolutions, Euler Products & Arithmetic Identities

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Verified Bound / Statement |
| :--- | :--- | :--- |
| Actual coprime Möbius factorization | `coprimeMobiusFactorization` | $f(n)\mathbf{1}_{(n,d)=1} = (\mu * g_d)(n)$, $g_d$ multiplicative |
| Infinite Euler product ($s > 1/2$) | `coprimeKernelEulerProduct` | $d \ne 0$, $s > 1/2 \implies \sum_{n \ge 1} g_d(n)n^{-s} = \prod_p \sum_k g_d(p^k)p^{-ks}$ |
| Local $s = 3/4$ Euler-factor bound | `coprimeEulerRatioBound` | $d \ne 0$, $r_2 = 2/3 \implies \prod_{p \mid d}(1 - r_p p^{-3/4})^{-1} \le \tau(d)$ |
| Uniform harmonic Möbius bound | `mobiusHarmonicBound` | $\forall N \ge 1,\; \|\sum_{n=1}^N \mu(n)/n\| \le 1$ |
| Laurent–exponential tail decay | `mobiusTailAntideriv`, `mobiusTailLogDecay` | Exact antiderivative of $z^3 e^{-cz}$ and $O_{c,A}(z^{-2A})$ bound |
| Vaughan, Baez–Duarte & signed-square | `vaughanIdentity`, `finiteEnergyExact`, `coprimeSignedSquare` | Dirichlet Vaughan split; $E_{\mathrm{tail}} = E_{\mathrm{trunc}} - 1$; `CommRing` identity |

### 3. Mellin Multipliers, Stieltjes Tails & Integral Obstructions

| Mathematical Result | Lean Declaration (`RhAstraSynthesis.MainTheorems`) | Verified Bound / Statement |
| :--- | :--- | :--- |
| Critical-strip tent non-vanishing | `tentMellinNonvanishing` | $0 < \operatorname{Re}(s) < 1 \implies \int_1^2 \tau(u)u^{s-1}\,\mathrm{d}u \ne 0$ |
| Prime-power Mellin–$\zeta'/\zeta$ identity | `primePowerMellinZeta` | $\operatorname{Re}(s) > 1$ dilated $-\zeta'(s)/\zeta(s)$ identity |
| Sharp critical-line tent gap | `tentHalfLineGap` | $\operatorname{Re}(s) = 1/2 \implies \|\mathrm{num}_\tau(s)\| \ge \sqrt{3} - 1 - 1/\sqrt{2} > 0$ |
| Non-outer off-axis tent zeros | `tentOffAxisZeros` | Infinitely many zeros of $\mathrm{num}_\tau$ in $2 < \operatorname{Re}(s) < 4$ |
| Floor-kernel $O(K^{-\gamma})$ transfer | `floorKernelErrorBound` | $\|G(t)\| \le C t^{-\gamma}$ ($0 < \gamma < 1$) Lebesgue error bound |
| Abel summation & polylogarithmic $L^1$ tails | `abelSummationInv`, `logDecayIntegrableTail` | $\|G(t)\| \le C(\log t)^{-1-\delta} \implies G(t)/t \in L^1([2,\infty))$ |
| Parity, Hardy defect & Pick minors | `parityPseudoDensityNonneg`, `modelSpaceDefectLowerBound`, `negMinorNotPosSemidef` | $1 + t^{-1/4}\cos(\omega\log t) \ge 0$; model-space defect $> 0$; $2\times 2$ minor refutation |

## Repository Layout

- [`lean/RhAstraSynthesis.lean`](lean/RhAstraSynthesis.lean) — Root import ordered by mathematical branch (`43` submodules).
- [`lean/RhAstraSynthesis/MainTheorems.lean`](lean/RhAstraSynthesis/MainTheorems.lean) — Theorem index and `#print axioms` checks (`[propext, Classical.choice, Quot.sound]`).
- [`lean/RhAstraSynthesis/TargetStatements.lean`](lean/RhAstraSynthesis/TargetStatements.lean) — Frozen statement interfaces with executable non-vacuity `example` witnesses.
- [`rocq/`](rocq/) — Independent Rocq `9.0` companion proving the finite rational signed-square envelope and sharpness counterexample (`rocqchk`).
- [`blueprint/src/content.tex`](blueprint/src/content.tex) — LaTeX blueprint linking informal theorems (`\leanok` vs `\notready`) directly to Lean identifiers ([PDF](blueprint/src/print.pdf)).
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — Module inventory.
- [`tests/`](tests/) — Boundary probes (`test_mathematical_probes.py`) and source integrity audit (`test_lean_integrity.py`).

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
