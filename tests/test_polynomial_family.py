"""Independent probes for the reciprocal polynomial-family specialization."""
import math
import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


class PolynomialFamilyTests(unittest.TestCase):
    def test_normalization_and_monomial_family(self):
        for L in (1, 4, 25):
            C, R = 2.0, 3.0
            for ratio in (0.0, 0.2, 0.75):
                r = R * ratio * math.exp(-2 / math.sqrt(L))
                sigma = (r / R) * math.exp(2 / math.sqrt(L))
                for s in range(7):
                    partial = 0.0
                    for m in range(1, 45):
                        # P_m = C R^(-m) X^m: samples satisfy the hypothesis.
                        term = C * (r / R) ** m if s == m else 0.0
                        partial += term
                        normalized = math.exp(2 * m / math.sqrt(L)) * R ** (-m) * r ** m
                        self.assertAlmostEqual(normalized, sigma ** m, delta=1e-12)
                        major = C * (8 * L) ** s / math.factorial(2 * s) * m ** (3 * s) * sigma ** m
                        self.assertLessEqual(term, major + 1e-12)
                    bound = C / (1 - sigma) * (64 * L / (1 - sigma) ** 3) ** s * math.factorial(s)
                    self.assertLessEqual(partial, bound)

    def test_family_interface_and_imports(self):
        source = (ROOT / 'lean/RhAstraSynthesis/ReciprocalGevreyMajorant.lean').read_text()
        for name in ('reciprocal_exponential_weight', 'polynomial_reciprocal_family_pointwise',
                     'polynomial_reciprocal_family_gevrey'):
            self.assertIn('theorem ' + name, source)
        self.assertIn('Polynomial.iterate_derivative_eq_zero', source)
        self.assertIn('polynomial_reciprocal_sample_factorial_bound', source)
        base = ROOT / 'lean'
        graph = {}
        for p in base.rglob('*.lean'):
            graph['.'.join(p.relative_to(base).with_suffix('').parts)] = re.findall(
                r'^import (RhAstraSynthesis(?:\.\w+)*)', p.read_text(), re.M)
        done, active = set(), set()
        def visit(n):
            self.assertNotIn(n, active, 'import cycle')
            if n in done:
                return
            active.add(n)
            for d in graph.get(n, []):
                visit(d)
            active.remove(n)
            done.add(n)
        for n in graph:
            visit(n)


if __name__ == '__main__':
    unittest.main()
