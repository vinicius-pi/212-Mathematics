"""Structural contracts for the complex profile bridge (not a Lean checker)."""
from fractions import Fraction as Q
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent.parent


class ComplexProfileContracts(unittest.TestCase):
    def test_actual_uniform_series_and_absolute_convergence(self):
        src = (ROOT / 'lean/Mathematics212/ReciprocalCoefficientProfile.lean').read_text(encoding='utf-8')
        for token in ('tendstoUniformlyOn_tsum_nat hs', 'norm_tsum_le_tsum_norm hn',
                      'Summable (fun n => ‖reciprocalProfileTerm P s n u‖)',
                      'polynomial_reciprocal_family_gevrey_all_radii',
                      '∑\' n, reciprocalProfileTerm P s n u',
                      '(s.factorial : ℝ)', 'P (n + 1)'):
            self.assertIn(token, src)
        # The quantified order must follow the existential radius parameter.
        self.assertLess(src.index('∃ L : ℕ'), src.index('∧ ∀ s : ℕ'))

    def test_exact_nonreal_geometric_boundary_and_tail(self):
        # P_m(t)=t, s=1: the profile is sum_{n>=0} u^(n+1).
        # Rational pairs avoid all floating-point approximations. This probes
        # the mathematics, not elaboration or kernel correctness of Lean.
        def add(z, w):
            return z[0] + w[0], z[1] + w[1]

        def mul(z, w):
            return z[0]*w[0] - z[1]*w[1], z[0]*w[1] + z[1]*w[0]

        def neg(z):
            return -z[0], -z[1]

        def norm_sq(z):
            return z[0]**2 + z[1]**2

        def div(z, w):
            d = norm_sq(w)
            return mul(z, (w[0]/d, -w[1]/d))

        zero, one = (Q(0), Q(0)), (Q(1), Q(0))
        r = Q(3, 4)
        # Include the boundary of a CLOSED subdisk and a point near |u|=1.
        for u, radius in (((Q(9, 20), Q(3, 5)), r),
                          ((Q(297, 500), Q(99, 125)), Q(99, 100))):
            self.assertEqual(norm_sq(u), radius**2)
            denominator = add(one, neg(u))
            total = div(u, denominator)
            power, partial = one, zero
            for N in range(41):
                tail = add(total, neg(partial))
                self.assertEqual(tail, div(mul(power, u), denominator))
                bound = radius**(N+1) / (1-radius)
                self.assertLessEqual(norm_sq(tail), bound**2)
                if N == 0:
                    self.assertEqual(partial, zero)  # no degree-zero term
                power = mul(power, u)
                partial = add(partial, power)
            self.assertLess(radius**41 / (1-radius), radius / (1-radius))

        # On the OUTER boundary |u|=R=1 the terms do not even tend to zero.
        u = (Q(3, 5), Q(4, 5))
        power = one
        for _ in range(40):
            power = mul(power, u)
            self.assertEqual(norm_sq(power), 1)

    def test_holomorphy_interface_and_blueprint_dependency(self):
        src = (ROOT / 'lean/Mathematics212/ReciprocalCoefficientProfile.lean').read_text(encoding='utf-8')
        self.assertIn('DifferentiableOn ℂ (reciprocalCoefficientProfile P s)', src)
        self.assertIn('hlocal.differentiableOn', src)
        tex = (ROOT / 'blueprint/src/content.tex').read_text(encoding='utf-8')
        block = tex.split('\\label{thm:reciprocal-profile-holomorphy}', 1)[1].split('\\end{proof}', 1)[0]
        self.assertIn('\\uses{thm:reciprocal-complex-profiles}', block)
        self.assertIn('polynomial_reciprocal_profiles_holomorphic', block)


if __name__ == '__main__':
    unittest.main()
