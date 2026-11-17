"""Structural contracts for the complex profile bridge (not a Lean checker)."""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent.parent


class ComplexProfileContracts(unittest.TestCase):
    def test_actual_uniform_series_and_absolute_convergence(self):
        src = (ROOT / 'lean/RhAstraSynthesis/ReciprocalCoefficientProfile.lean').read_text(encoding='utf-8')
        for token in ('tendstoUniformlyOn_tsum_nat hs', 'norm_tsum_le_tsum_norm hn',
                      'Summable (fun n => ‖reciprocalProfileTerm P s n u‖)',
                      'polynomial_reciprocal_family_gevrey_all_radii',
                      '∑\' n, reciprocalProfileTerm P s n u',
                      '(s.factorial : ℝ)', 'P (n + 1)'):
            self.assertIn(token, src)
        # The quantified order must follow the existential radius parameter.
        self.assertLess(src.index('∃ L : ℕ'), src.index('∧ ∀ s : ℕ'))

    def test_status_does_not_claim_kernel_verification(self):
        tex = (ROOT / 'blueprint/src/content.tex').read_text(encoding='utf-8')
        block = tex.split('\\label{thm:reciprocal-complex-profiles}', 1)[1].split('\\end{proof}', 1)[0]
        self.assertNotIn('\\leanok', block)
        self.assertIn('not yet compiled or axiom-audited', block)
        self.assertIn('fractional-grid target remain open', block)


if __name__ == '__main__':
    unittest.main()
