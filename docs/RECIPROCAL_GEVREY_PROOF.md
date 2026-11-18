# Reciprocal Gevrey-1 expansion

Let `P_m` be real polynomials of degree at most `m`, with
`|P_m(1/k)| ≤ C R^(-m)` for every positive `m,k`, where `C,R > 0`.
For each `0 ≤ r < R`, choose one natural `L > 0` with
`d = 1 - (r/R) exp(2/√L) > 0`.

Writing `q_n(u) = 1 + ∑_{m≥1} P_m(1/n) u^m` and
`F_s(u) = ∑_{m≥1} ([X^s]P_m) u^m`, the final estimate is

```text
|q_n(u) - (1 + ∑_{s<p} F_s(u) n^(-s))|
  ≤ (3C/d) (72L/d³)^p p! / n^p.
```

The estimate holds simultaneously for all positive `n,p` and all `|u| ≤ r`.
The full zeroth profile is `1 + F_0`; the expansion in `1/n` is asymptotic as
`n → ∞` at fixed truncation order `p`, while each profile series `F_s(u)`
converges in `u` on the open disk `|u| < R`.

## Interface distinctions

- `Mathematics212.polynomial_reciprocal_gevrey_expansion` exports the
  conjunction of sampled absolute summability (`reciprocal_sampled_summable`),
  the complex remainder identity (`reciprocal_complex_remainder_identity`), and
  the norm estimate, while proving absolute summability of the complex
  remainder series internally (`hnorm`).
- `Mathematics212.TargetStatements.reciprocal_gevrey_expansion` projects only
  the norm estimate (via `.2.2`).
- `Mathematics212.polynomial_reciprocal_profiles_all_radii` and
  `Mathematics212.polynomial_reciprocal_profiles_holomorphic` are companion
  theorems for uniform convergence on closed subdisks and holomorphy on `|u| < R`.
- Open Analytic Extensions (see `sec:open-questions` / `Open Mathematical Questions`
  in the blueprint PDF) remain unformalized targets.

## Proof chain

| Stage | Declaration |
|---|---|
| Good-set measure | `polynomial_reciprocal_good_measure` |
| Interval control | `polynomial_reciprocal_remez_exponential_bound` |
| Uniform derivatives | `polynomial_reciprocal_sample_factorial_bound` |
| Geometric summation | `geometric_power_moment` |
| Factorial majorant | `cubic_geometric_gevrey_majorant` |
| Radius choice | `exists_reciprocal_gevrey_parameter` |
| Profile convergence | `polynomial_reciprocal_profiles_all_radii` |
| Profile holomorphy | `polynomial_reciprocal_profiles_holomorphic` |
| Small-degree remainder | `polynomial_reciprocal_taylor_remainder_bound` |
| Complementary remainder | `polynomial_reciprocal_large_degree_remainder_bound` |
| Absolute remainder series | `polynomial_reciprocal_family_remainder_gevrey` |
| Complex identity | `reciprocal_complex_remainder_identity` |
| Complete expansion | `polynomial_reciprocal_gevrey_expansion` |

## Verification

- Frozen candidate revision `08ec36676a072a6107e9d76a43f268f907ed0734` passed
  [CI run 44358503398](https://github.com/vinicius-pi/212-Mathematics/actions/runs/44358503398)
  (`verify` + `verify-rocq`).
- Historical proof-chain receipts: revision `579561b49aeacc6923c2e175cac063559cc2bdc6`
  passed [CI run 44012564508](https://github.com/vinicius-pi/212-Mathematics/actions/runs/44012564508);
  consolidated revision `9b60bb8f60a7a171fdc561ae4ea0b3846f7d4599` passed
  [CI run 44029922271](https://github.com/vinicius-pi/212-Mathematics/actions/runs/44029922271).
- The workflow compiles the Lean package, runs `leanchecker`, audits axioms under
  `Mathematics212`, and executes Python probes alongside the finite rational
  Rocq verification (`rocq/verify_rocq.py`).
