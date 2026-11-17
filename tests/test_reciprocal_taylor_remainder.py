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
