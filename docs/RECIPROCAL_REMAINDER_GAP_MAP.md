# Reciprocal Gevrey-1 remainder: candidate bridge ledger

## Verification boundary

Base revision: `b8ab406`, branch `feat/reciprocal-gevrey-bridge`.
The new Lean declarations in this working tree are **uncompiled**. No local
Lean, Lake, Rocq or Docker execution was attempted; compilation is delegated
to parent CI. No commit or push was made. Python unittest discovery passed
31 tests; `git diff --check` passed. These checks are not Lean certificates.

Public pinned Mathlib source inspected at revision
`5ed2965256430c3649e86755f9576b54eca72435`: the finite-sum absolute-value
inequality, field-order inequality usage, and existing project factorial and
geometric moment APIs. One guessed public source path returned 404; the correct
`Degree/Defs.lean` path was subsequently retrieved. No private sources used.

## Candidate mathematical artifacts

- `reciprocal_coefficient_bound`: zero-point coefficient majorant for **all**
  orders. For `s>m`, uses vanishing of the algebraic iterated derivative and
  the already established normalized derivative/coefficient identity.
- `polynomial_reciprocal_large_degree_remainder_bound`: direct estimate for
  `1≤n≤Lm`, including equality and `p=0`. Exact requested degree powers
  `m^(p+2s)` and denominator `(2s)!` are retained. No assumption `p≤m`.
- `factorial_mixed_moment_le` and its real quotient form:
  `(p+2s)!/(2s)! ≤ 8^p p!` for `s≤p`.
- `mixed_geometric_gevrey_moment`: positive-index mixed-moment summability
  plus the explicit bound `8^p p!/(1-σ)^(p+2s+1)`.
- `finite_mixed_geometric_bound`: finite Taylor-index sum collapsed to
  `d⁻¹ ((1+8/d²)/d)^p`, where `d=1-σ>0`.
- TargetStatements distinguishes these finite/summability bridges from the
  full profile remainder. Added exact nonzero `X²` probe at `n=3<Lm=4`,
  above-degree truncation at `p=4`, and a mixed-index factorial example.

## Remaining proof obligations, in dependency order

1. Compile the exact working tree and audit the new declarations. In particular,
   check casts, finite-sum rewrites, cancellation of reciprocal powers, and the
   availability/signatures of `Summable.div_const`, `tsum_div_const`, and
   `one_le_pow₀` in the pinned revision. No compiler failures have yet occurred.
2. Specialize the large-degree estimate to `B_m=C R^(-m)` and multiply by
   `r^m`. Set `τ=r/R`, `σ=τ exp(2/sqrt L)<1`, `d=1-σ`. The sample term
   has weight `τ^m≤σ^m`; the coefficient terms have weight exactly `σ^m`.
3. Sum the indicator-restricted large-degree terms using the mixed moments.
   Prove summability before any tsum inequality/interchange. The finite
   Taylor-index sum may be interchanged with tsum only after this step.
   The explicit resulting scaled bound is

   `C/d * (L/d)^p * p!`
   `+ C/d * (8*L*(1+8/d²)/d)^p * p!`.

   Since `0<d≤1`, this is at most
   `2*C/d * (72*L/d³)^p * p!`. The finite geometric and mixed-factorial
   ingredients are now separate candidate Lean results, but this combined
   family inequality is **not yet a Lean declaration**.
4. Sum the complementary small-degree terms by the existing cubic moment
   majorant after dividing the finite remainder by `n^p`. Its bound is
   `C/d * (64*L/d³)^p * p! * n^(-p)`. Combining the two regimes permits
   the uniform bound `3*C/d * (72*L/d³)^p * p! * n^(-p)` for `p>0`.
   Both estimates include `n=Lm`; choose one side in the formal partition
   to avoid double counting. All sequences use `m=k+1`, never `m=0`.
5. Define the sampled complex family series, establish absolute convergence
   uniformly on each closed subdisk from the sample bound, and identify its
   difference from the finite coefficient-profile expansion with the sum of
   polynomial remainders. This needs the real normalized-derivative/coefficient
   identity, complex casts, finite-sum/tsum interchange, and norm control.
6. Quantify the radius parameter before every order and sample index using
   `exists_reciprocal_gevrey_parameter`. Treat `p=0` separately from the
   Lagrange theorem (the large-degree candidate already admits order zero).
   Ensure uniformity on the entire closed complex subdisk, including `r=0`.
7. Only after all these checks promote a **reciprocal Gevrey-1** remainder
   theorem. The blueprint's fractional-grid Gevrey-alpha proposition remains
   separate and open; none of these bridges supplies that extension.
