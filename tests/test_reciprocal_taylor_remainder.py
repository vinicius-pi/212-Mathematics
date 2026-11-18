"""Executable mathematical probes, not substitutes for Lean compilation."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import comb, factorial
import unittest


def evaluate(coeffs, x):
    return sum((a * x**s for s, a in enumerate(coeffs)), Q(0))


def remainder(coeffs, p, x):
    return evaluate(coeffs, x) - evaluate(coeffs[:p], x)


def integral_remainder(coeffs, p, x):
    # Integrate P^(p)(t) (x-t)^(p-1)/(p-1)! by expanding both
    # factors. Every operation is rational, including at the boundary.
    total = Q(0)
    for s in range(p, len(coeffs)):
        d = coeffs[s] * factorial(s) / factorial(s - p)
        for j in range(p):
            total += (d * comb(p - 1, j) * (-1)**j * x**(p - 1 - j)
                      * x**(s - p + j + 1)
                      / (s - p + j + 1) / factorial(p - 1))
    return total


def dec(x):
    return Decimal(x.numerator) / Decimal(x.denominator)


class ReciprocalTaylorRemainderProbes(unittest.TestCase):
    def test_boundary_and_beyond_with_signed_polynomials(self):
        count = 0
        with localcontext() as ctx:
            ctx.prec = 70
            for m in range(1, 8):
                coeffs = [Q((-1)**s * (s + 1), m + 1) for s in range(m + 1)]
                # This B bounds every reciprocal sample since 0 < 1/k <= 1.
                B = sum(map(abs, coeffs))
                for L in (1, 2, 9):
                    for n in (L * m, L * m + 1, 10 * L * m):
                        x = Q(1, n)
                        self.assertLessEqual(x, Q(1, L * m))
                        for p in range(1, m + 3):
                            r = remainder(coeffs, p, x)
                            self.assertEqual(r, integral_remainder(coeffs, p, x))
                            rhs = ((Decimal(2 * m) / Decimal(L).sqrt()).exp()
                                   * dec(B) * Decimal((8 * L)**p * m**(3 * p))
                                   / Decimal(factorial(2 * p) * n**p))
                            self.assertLessEqual(dec(abs(r)), rhs)
                            if p > m:
                                self.assertEqual(r, 0)
                            count += 1
        self.assertEqual(count, 378)

    def test_nonzero_boundary_witness(self):
        coeffs = [Q(0), Q(0), Q(1)]
        self.assertEqual(remainder(coeffs, 2, Q(1, 4)), Q(1, 16))
        self.assertEqual(integral_remainder(coeffs, 2, Q(1, 4)), Q(1, 16))
        self.assertEqual(remainder(coeffs, 3, Q(1, 4)), 0)

    def test_small_degree_segment_hypothesis_is_substantive(self):
        L, m = 3, 2
        self.assertGreater(Q(1, L * m - 1), Q(1, L * m))
        self.assertEqual(Q(1, L * m), Q(1, 6))

    def test_large_degree_scaled_bound_exact(self):
        # The exponential is >= 1. Test the stronger algebraic estimate with
        # our l1 coefficient bound B, including p=0 and every s>m zero term.
        count = 0
        for m in range(1, 9):
            coeffs = [Q((-1)**s * (s + 1), m + 1) for s in range(m + 1)]
            B = sum(map(abs, coeffs))
            for L in (1, 2, 5):
                for n in sorted({1, max(1, L * m - 1), L * m}):
                    for p in range(m + 4):
                        lhs = n**p * abs(remainder(coeffs, p, Q(1, n)))
                        rhs = B * L**p * m**p + B * L**p * sum(
                            (Q(8**s * m**(p + 2*s), factorial(2*s))
                             for s in range(p)), Q(0))
                        self.assertLessEqual(lhs, rhs)
                        for s in range(m + 1, p):
                            self.assertEqual(coeffs[s] if s < len(coeffs) else 0, 0)
                        count += 1
        self.assertGreater(count, 500)

    def test_mixed_factorials_and_finite_geometric_collapse(self):
        for p in range(21):
            for s in range(p + 1):
                self.assertLessEqual(factorial(p + 2*s),
                                     8**p * factorial(2*s) * factorial(p))
            for sigma in (Q(0), Q(1, 2), Q(9, 10)):
                d = 1 - sigma
                finite = sum((Q(8**s, 1) / d**(p + 2*s + 1)
                              for s in range(p)), Q(0))
                geometric = (1 + 8 / d**2)**p / d**(p + 1)
                self.assertLessEqual(finite, geometric)
                # Mixed-moment factorial loss and the finite s-sum collapse
                # to a single order-p factorial with a radius-only base.
                self.assertLessEqual(8**p * finite * factorial(p),
                                     Q(1, 1) / d * (72 / d**3)**p * factorial(p))

    def test_infinite_nonzero_weighted_family_and_global_majorant(self):
        # P_m = 2^(-m) X^m satisfies the original hypotheses with C=1,R=2.
        # The exact infinite remainder is a geometric tail, not a truncation.
        L, R, radius = 16, Q(2), Q(1, 2)
        with localcontext() as ctx:
            ctx.prec = 70
            sigma = dec(radius / R) * (Decimal(2) / Decimal(L).sqrt()).exp()
            self.assertLess(sigma, 1)
            d = 1 - sigma
            for n in (1, 16, 32, 80):
                for p in range(1, 7):
                    q = radius / (R * n)
                    exact = q**p / (1 - q)
                    self.assertGreater(exact, 0)
                    partial = sum((q**m for m in range(p, 41)), Q(0))
                    self.assertEqual(exact - partial, q**41 / (1 - q))
                    bound = (Decimal(3) / d * (Decimal(72 * L) / d**3)**p
                             * Decimal(factorial(p)) / Decimal(n**p))
                    self.assertLessEqual(dec(exact), bound)
                    for m in range(1, 21):
                        coeffs = [Q(0)] * m + [R**(-m)]
                        lhs = dec(n**p * abs(remainder(coeffs, p, Q(1, n))) * radius**m)
                        small = (Decimal((8 * L)**p * m**(3*p))
                                 / Decimal(factorial(2*p)) * sigma**m)
                        sample = Decimal(L**p * m**p) * sigma**m
                        mixed = Decimal(L**p) * sum(
                            (Decimal(8**s * m**(p + 2*s)) / Decimal(factorial(2*s))
                             * sigma**m for s in range(p)), Decimal(0))
                        self.assertLessEqual(lhs, small + sample + mixed)
                        self.assertLessEqual(lhs, small if L*m <= n else sample + mixed)
            # Radius-only base comparisons used by the Lean composition.
            self.assertLessEqual(Decimal(L) / d, Decimal(72*L) / d**3)
            self.assertLessEqual(Decimal(8*L) * (1 + 8/d**2) / d,
                                 Decimal(72*L) / d**3)

    def test_lagrange_factorial_not_vector_bound_factorial(self):
        # For X^p the normalized p-th derivative is exactly 1, and the
        # remainder is x^p. Using the vector mean bound loses a factor p.
        for p in range(1, 9):
            x = Q(1, p + 1)
            coeffs = [Q(0)] * p + [Q(1)]
            self.assertEqual(remainder(coeffs, p, x), x**p)
            self.assertEqual(Q(factorial(p), factorial(p - 1)), p)


if __name__ == '__main__':
    unittest.main()
