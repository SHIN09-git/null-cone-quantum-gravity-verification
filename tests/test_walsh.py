"""Exact finite-block checks for the two-cut construction in the report."""
import unittest
from fractions import Fraction


class WalshTests(unittest.TestCase):
    def test_unitarity_and_block_masses(self):
        for j in (1, 2, 3):
            dimension = 4**j
            rows = [[(-1)**((a & b).bit_count() % 2) for b in range(dimension)]
                    for a in range(dimension)]
            for i, first in enumerate(rows):
                for k, second in enumerate(rows):
                    inner = sum(a*b for a, b in zip(first, second))
                    self.assertEqual(inner, dimension if i == k else 0)
            weight = Fraction(1, 2**j * dimension * 2**j)
            self.assertEqual(sum(sum(row) for row in rows) * weight, Fraction(1, 4**j))
            self.assertEqual(sum(abs(a) for row in rows for a in row) * weight, 1)
