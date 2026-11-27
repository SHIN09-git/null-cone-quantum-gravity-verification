"""Replay the five equal-rank cuts with the Phase 2 complex operator."""

import unittest
from math import cos, exp, isclose

from phase2.calculations.independent import compare


def striped(even_count, odd_count):
    return set(range(0, 2 * even_count, 2)) | set(range(1, 2 * odd_count, 2))


class EqualRankChecks(unittest.TestCase):
    def test_cutoffs_against_the_exchange_operator(self):
        scale = exp(-3) * (1 - cos(1))
        previous = {}
        for n in range(1, 33):
            first = striped(5 * n, n)
            for name, even_count, expected in (
                ("aligned", 5 * n, 6 * n),
                ("positive", 2 * n + 1, 2),
                ("zero", 2 * n, 0),
                ("negative", 2 * n - 1, -2),
                ("opposed", n, -2 * n),
            ):
                with self.subTest(route=name, n=n):
                    second = striped(even_count, 6 * n - even_count)
                    self.assertEqual((len(first), len(second)), (6 * n, 6 * n))
                    self.assertTrue(set(range(2 * n)) <= first & second)
                    self.assertEqual(2 * len(first & second) - 6 * n, expected)
                    cut = {(j, "L") for j in first} | {(j, "R") for j in second}
                    self.assertTrue(previous.get(name, set()) < cut)
                    previous[name] = cut
                    _, signed = compare(cut)
                    self.assertTrue(isclose(signed / scale, expected, rel_tol=1e-11,
                                            abs_tol=1e-10))


if __name__ == "__main__":
    unittest.main()
