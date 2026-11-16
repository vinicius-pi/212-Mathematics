#!/usr/bin/env python3
"""Exact rational and high-precision boundary/counterexample probes for RhAstraSynthesis.

These probes independently verify boundary cases and counterexamples (e.g., why d != 0,
r_2 = 2/3, negative affine slopes, and the cubic sharpness witness are tight). They do
not replace Lean kernel verification (`lake build` + `leanchecker`).
"""
from decimal import Decimal, localcontext
from fractions import Fraction
import cmath
from math import comb, cos, exp, factorial, gcd, log, pi, prod, sin, sqrt
import unittest


def mu(n: int) -> int:
    if n == 1:
        return 1
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def prime_factors(n: int) -> list[int]:
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def psi(n: int) -> int:
    return 0 if n == 0 else prod(p + 1 for p in prime_factors(n))


def r_weight(n: int) -> Fraction:
    return Fraction(1) if n == 0 else prod((Fraction(p, p + 1) for p in prime_factors(n)), start=Fraction(1))


def g_kernel(d: int, n: int) -> Fraction:
    if n == 0:
        return Fraction(0)
    return prod(
        (Fraction(1) if d % p == 0 else Fraction(1, p + 1) for p in prime_factors(n)),
        start=Fraction(1),
    )


def chebyshev_T_poly(n: int) -> list[Fraction]:
    if n == 0:
        return [Fraction(1)]
    if n == 1:
        return [Fraction(0), Fraction(1)]
    t0, t1 = [Fraction(1)], [Fraction(0), Fraction(1)]
    for _ in range(2, n + 1):
        two_x_t1 = [Fraction(0)] + [2 * c for c in t1]
        nxt = [
            (two_x_t1[i] if i < len(two_x_t1) else Fraction(0))
            - (t0[i] if i < len(t0) else Fraction(0))
            for i in range(max(len(two_x_t1), len(t0)))
        ]
        t0, t1 = t1, nxt
    return t1


def poly_mul(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        for j, cb in enumerate(b):
            out[i + j] += ca * cb
    return out


def eval_poly(coeffs: list[Fraction], x: Fraction) -> Fraction:
    acc = Fraction(0)
    for c in reversed(coeffs):
        acc = acc * x + c
    return acc


class MathematicalProbesTests(unittest.TestCase):
    def test_uniform_reciprocal_factorial_half_segments(self):
        # Exact rational probes, including order zero, midpoint, both endpoints,
        # both orientations, and the highest nonzero derivative. Not a Lean check.
        for m in range(1, 8):
            for L in (Fraction(1, 3), Fraction(1), Fraction(5, 2)):
                width = 1 / (L * m)
                half = width / 2
                coeffs = chebyshev_T_poly(m)
                for j in range(9):
                    x = width * Fraction(j, 8)
                    a = 1 if x <= half else -1
                    for k in range(5):
                        image = x + a * half * Fraction(k, 4)
                        self.assertLessEqual(0, image)
                        self.assertLessEqual(image, width)
                    cur = coeffs
                    for s in range(m + 1):
                        # P(t) = T_m(2*L*m*t - 1), uniformly bounded by one.
                        value = (2 * L * m) ** s * eval_poly(cur, 2 * L * m * x - 1)
                        bound = (8 * L) ** s * m ** (3 * s) / factorial(2 * s)
                        self.assertLessEqual(abs(value) / factorial(s), bound)
                        cur = [i * cur[i] for i in range(1, len(cur))]

    def test_cubic_sharpness_witness_and_quadratic_obstruction(self):
        for m in range(1, 8):
            ann = [Fraction(1)]
            for j in range(1, m + 1):
                ann = poly_mul(ann, [Fraction(1), Fraction(-j)])
            t_coeffs = chebyshev_T_poly(m)
            base = [Fraction(1), Fraction(-2 * m)]
            comp, pwr = [Fraction(0)], [Fraction(1)]
            for c in t_coeffs:
                term = [c * p for p in pwr]
                comp = [
                    (comp[i] if i < len(comp) else Fraction(0))
                    + (term[i] if i < len(term) else Fraction(0))
                    for i in range(max(len(comp), len(term)))
                ]
                pwr = poly_mul(pwr, base)
            witness = poly_mul(ann, comp)
            self.assertLessEqual(len(witness) - 1, 2 * m)
            self.assertEqual(abs(witness[1]), 2 * m**3 + Fraction(m * (m + 1), 2))
            self.assertGreater(abs(witness[1]), m**2)
            for n in range(1, 25):
                val = eval_poly(witness, Fraction(1, n))
                if n <= m:
                    self.assertEqual(val, 0)
                else:
                    self.assertLessEqual(abs(val), 1)

    def test_coprime_kernel_factorization_and_zero_modulus_counterexample(self):
        for d in (1, 2, 3, 6, 12, 30):
            for n in range(1, 45):
                conv = sum(
                    Fraction(mu(a)) * g_kernel(d, n // a)
                    for a in range(1, n + 1)
                    if n % a == 0
                )
                expected = Fraction(mu(n)) * r_weight(n) if gcd(n, d) == 1 else Fraction(0)
                self.assertEqual(conv, expected)
                self.assertEqual(g_kernel(d, n), Fraction(psi(gcd(n, d)), psi(n)))
                self.assertLessEqual(g_kernel(d, n), psi(d) * g_kernel(1, n))
        # Boundary necessity: d = 0 violates g_d(n) <= psi(d) * g_1(n)
        self.assertGreater(g_kernel(0, 2), psi(0) * g_kernel(1, 2))

    def test_euler_factor_p2_requires_r2_weight(self):
        with localcontext() as ctx:
            ctx.prec = 50
            two_neg_34 = Decimal(2) ** Decimal("-0.75")
            unweighted = 1 / (1 - two_neg_34)
            weighted = 1 / (1 - (Decimal(2) / 3) * two_neg_34)
            self.assertGreater(unweighted, 2)
            self.assertLess(unweighted, Decimal("2.5"))
            self.assertLess(weighted, 2)
            for d in range(1, 40):
                factors = prime_factors(d)
                prod_ratio = Decimal(1)
                for p in factors:
                    rp = Decimal(p) / Decimal(p + 1)
                    ratio = 1 / (1 - rp * (Decimal(p) ** Decimal("-0.75")))
                    self.assertLess(ratio, 2)
                    prod_ratio *= ratio
                tau_d = sum(1 for k in range(1, d + 1) if d % k == 0)
                self.assertLessEqual(prod_ratio, Decimal(tau_d))

    def test_remez_chebyshev_envelope_and_gevrey_factorial(self):
        for m in (1, 3, 8, 15):
            poly = chebyshev_T_poly(m)
            for L in (1, 4, 9, 25):
                x = Fraction(1) + Fraction(2, L)
                self.assertLessEqual(float(eval_poly(poly, x)), exp(2.0 * m / sqrt(L)) * (1 + 1e-12))
        for s in range(0, 10):
            self.assertLessEqual(comb(3 * s, s), 8**s)
        # Constant 4^s is false at s = 3
        self.assertGreater(comb(9, 3), 4**3)

    def test_harmonic_mobius_and_laurent_exponential_tail(self):
        harmonic = Fraction(0)
        for n in range(1, 101):
            harmonic += Fraction(mu(n), n)
            self.assertLessEqual(abs(harmonic), 1)
            self.assertEqual(sum(mu(k) * (n // k) for k in range(1, n + 1)), 1)
        for c in (Fraction(1, 3), Fraction(2), Fraction(7, 5)):
            p = [12 / c**4, 12 / c**3, 6 / c**2, 2 / c]
            deriv = [(i + 1) * p[i + 1] if i < 3 else Fraction(0) for i in range(4)]
            self.assertEqual([deriv[i] - c * p[i] for i in range(4)], [0, 0, 0, -2])

    def test_fractional_grid_sqrt_sharpness_and_remez_envelope(self):
        with localcontext() as ctx:
            ctx.prec = 50
            for m in (1, 3, 6):
                for n in range(1, 60):
                    x = Decimal(1) / Decimal(n).sqrt()
                    ann = Decimal(1)
                    for j in range(1, m + 1):
                        ann *= 1 - Decimal(j).sqrt() * x
                    arg = 1 - 2 * Decimal(m).sqrt() * x
                    t0, t1 = Decimal(1), arg
                    if m == 0:
                        tm = t0
                    else:
                        for _ in range(2, m + 1):
                            t0, t1 = t1, 2 * arg * t1 - t0
                        tm = t1
                    val = abs(ann * tm)
                    if n <= m:
                        self.assertLess(val, Decimal("1e-40"))
                    else:
                        self.assertLessEqual(val, Decimal(1) + Decimal("1e-40"))
                exact_d1 = 2 * Decimal(m) ** Decimal("2.5") + sum(
                    Decimal(j).sqrt() for j in range(1, m + 1)
                )
                self.assertGreater(exact_d1, Decimal(m * m))
        # Bernoulli fractional envelope: (1 + 1/L)^alpha <= 1 + alpha/L
        for alpha in (0.25, 0.5, 0.75, 1.0):
            for L in (4.0, 9.0, 25.0):
                self.assertLessEqual((1.0 + 1.0 / L) ** alpha, 1.0 + alpha / L + 1e-12)

    def test_tent_critical_line_gap_and_off_axis_zeros(self):
        gap = sqrt(3.0) - 1.0 - 1.0 / sqrt(2.0)
        self.assertGreater(gap, 0.024)
        for t in (0.0, 1.5, 10.0, 42.3, 123.7):
            s = complex(0.5, t)
            num = 1.0 + 2.0 ** (s - 1.0) - 2.0 * ((4.0 / 3.0) ** (s - 1.0))
            self.assertGreaterEqual(abs(num) + 1e-12, gap)
        # Off-axis zero in 2 < Re(s) < 4 via the contracting fixed-point band (k = 12)
        ln2, ln32 = log(2.0), log(1.5)
        sig0 = ln2 / ln32
        t_per = 2.0 * pi / ln32
        w = complex(2.26, 12.0 * t_per)
        for _ in range(40):
            w = complex(sig0, 12.0 * t_per) - cmath.log(1.0 + cmath.exp(-w * ln2)) / ln32
        s = w + 1.0
        self.assertGreater(s.real, 2.0)
        self.assertLess(s.real, 4.0)
        self.assertLess(abs(1.0 + 2.0 ** (s - 1.0) - 2.0 * ((4.0 / 3.0) ** (s - 1.0))), 1e-12)

    def test_stieltjes_abel_summation_and_parity_pick(self):
        a = [0] + [mu(n) for n in range(1, 50)]
        S = [sum(a[: k + 1]) for k in range(50)]
        for u, N in ((1, 20), (5, 40), (12, 49)):
            lhs = sum(Fraction(a[n], n) for n in range(u + 1, N + 1))
            rhs = Fraction(S[N], N) - Fraction(S[u], u) + sum(
                Fraction(S[n]) * (Fraction(1, n) - Fraction(1, n + 1)) for n in range(u, N)
            )
            self.assertEqual(lhs, rhs)
        for t in (1.0, 2.5, 17.0, 1000.0):
            for w in (0.5, 2.26618, 10.0):
                self.assertGreaterEqual(1.0 + (t ** (-0.25)) * cos(w * log(t)), 0.0)
        # Pick/Hankel 2x2 negative minor counterexample: v^T A v < 0
        aii, aij, ajj = 1.0, 2.0, 1.0  # det = 1 - 4 < 0
        v = (-aij, aii)
        quad = v[0] ** 2 * aii + 2 * v[0] * v[1] * aij + v[1] ** 2 * ajj
        self.assertLess(quad, 0.0)

    def test_bernstein_and_markov_interior(self):
        # Exact Chebyshev polynomials T_n via recurrence T_0=1, T_1=x, T_{n+1}=2xT_n - T_{n-1}
        def cheb_coeffs(n):
            if n == 0:
                return [Fraction(1)]
            if n == 1:
                return [Fraction(0), Fraction(1)]
            t0, t1 = [Fraction(1)], [Fraction(0), Fraction(1)]
            for _ in range(2, n + 1):
                shifted = [Fraction(0)] + [2 * c for c in t1]
                nxt = [shifted[i] - (t0[i] if i < len(t0) else 0) for i in range(len(shifted))]
                t0, t1 = t1, nxt
            return t1

        def poly_deriv(c):
            return [i * c[i] for i in range(1, len(c))]

        def poly_eval(c, x):
            acc = Fraction(0)
            for coef in reversed(c):
                acc = acc * x + coef
            return acc

        for n in range(1, 7):
            c = cheb_coeffs(n)
            dc = poly_deriv(c)
            # Bernstein / Van der Corput-Schaake equality on T_n at interior angles
            for k in range(1, 12):
                theta = k * pi / 13.0
                x, s = cos(theta), sin(theta)
                val = sum(float(coef) * (x ** i) for i, coef in enumerate(c))
                dval = sum(float(coef) * (x ** i) for i, coef in enumerate(dc))
                self.assertAlmostEqual(n * n * val * val + (dval * s) ** 2, float(n * n), places=9)
            # Iterated Markov interior bound on [-1, 1] and endpoint equality at s = 1 (n^2)
            cur = c
            prod_bnd = Fraction(1)
            for s in range(min(3, n) + 1):
                for num in range(-4, 5):
                    x = Fraction(num, 4)
                    self.assertLessEqual(abs(poly_eval(cur, x)), prod_bnd)
                if s == 1:
                    self.assertEqual(abs(poly_eval(cur, Fraction(1))), Fraction(n * n))
                prod_bnd *= Fraction((n - s) ** 2)
                cur = poly_deriv(cur)
        # Interior interval transfer on [0, 1/(L*m)] with L = 2, m = 4 (endpoints and midpoint)
        L, m = Fraction(2), 4
        c4 = cheb_coeffs(m)
        dc4 = poly_deriv(c4)
        for u in (Fraction(0), Fraction(1, 16), Fraction(1, 8)):
            x = 2 * L * m * u - 1
            d_at_u = 2 * L * m * poly_eval(dc4, x)
            self.assertLessEqual(abs(d_at_u), (2 * L * m) * Fraction(m * m))

    def test_measurable_remez_and_markov_derivative(self):
        # Exact Chebyshev polynomials T_n on multi-interval / disconnected E subset [a, b]
        def cheb_eval(n, x):
            if n == 0:
                return 1.0
            if n == 1:
                return x
            t0, t1 = 1.0, x
            for _ in range(2, n + 1):
                t0, t1 = t1, 2.0 * x * t1 - t0
            return t1

        # E = [0, 0.4] union [1.6, 2.0] subset [0, 2], |E| = 0.8, 2|I|/|E| - 1 = 4.0
        a, b = 0.0, 2.0
        e_len = 0.8
        y_arg = 2.0 * (b - a) / e_len - 1.0
        self.assertAlmostEqual(y_arg, 4.0, places=12)

        def eval_poly(coeffs, x):
            acc = 0.0
            for c in reversed(coeffs):
                acc = acc * x + c
            return acc

        def deriv_coeffs(coeffs):
            return [i * coeffs[i] for i in range(1, len(coeffs))]

        samples_e = [i * 0.001 for i in range(401)] + [1.6 + i * 0.001 for i in range(401)]
        samples_i = [i * 0.002 for i in range(1001)]
        test_polys = [
            [1.0, -2.0, 1.5],
            [0.5, -1.0, 0.25, 0.75],
            [1.0, 0.0, -3.0, 0.5, 0.4],
        ]
        for coeffs in test_polys:
            n = len(coeffs) - 1
            B = max(abs(eval_poly(coeffs, t)) for t in samples_e)
            remez_bound = cheb_eval(n, y_arg) * B
            for x in samples_i:
                self.assertLessEqual(abs(eval_poly(coeffs, x)), remez_bound + 1e-9)
            cur = coeffs
            markov_prod = 1.0
            for s in range(1, n + 1):
                markov_prod *= (n - (s - 1)) ** 2
                cur = deriv_coeffs(cur)
                deriv_bound = ((2.0 / (b - a)) ** s) * markov_prod * remez_bound
                for x in samples_i:
                    self.assertLessEqual(abs(eval_poly(cur, x)), deriv_bound + 1e-8)


if __name__ == "__main__":
    unittest.main()
