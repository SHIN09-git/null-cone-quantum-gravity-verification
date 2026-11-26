"""Check cutoffs by enumerating matrix entries independently of the closed formulas."""
import unittest
from fractions import Fraction
from itertools import combinations, product


class ClosureChecks(unittest.TestCase):
    def test_arbitrary_trimmed_flip_pairs(self):
        # Two labels per copy. O=-F x F contributes only when both partners survive.
        basis = list(product(range(4), (0,1)))
        for k in range(1,len(basis)+1):
            for selection in combinations(basis,k):
                cut = set(selection)
                offdiag = sum((j,1-a) in cut for j,a in cut)
                double = len({j for j,a in cut if a == 0 and (j,1) in cut})
                self.assertEqual(Fraction(offdiag)-Fraction(k,2), 2*double-Fraction(k,2))

    def test_constant_same_positive_scalar_exhaustion(self):
        previous = set()
        for n in range(1,35):
            cur = {(i,0) for i in range(3*n-2)} | {(i,1) for i in range(n)}
            self.assertLess(previous,cur)
            self.assertTrue(all((i,a) in cur for i in range(n) for a in (0,1)))
            matched = sum((i,1-a) in cur for i,a in cur)
            self.assertEqual(matched-Fraction(len(cur),2),1)
            self.assertEqual(Fraction(matched,len(cur))-Fraction(1,2),Fraction(1,len(cur)))
            previous = cur

    def test_joint_sums_from_individual_energy_and_area_labels(self):
        v = (Fraction(2,3),Fraction(1,3))
        for n in (1,9,42):
            rectangle = [v[a]*(int(a == 0)-v[0])/i for i in range(1,n+1) for a in (0,1)]
            self.assertEqual(sum(rectangle),0)
            self.assertEqual(sum(map(abs,rectangle)),2*v[0]*v[1]*sum(Fraction(1,i) for i in range(1,n+1)))
            different = rectangle+[v[1]*(-v[0])/i for i in range(n+1,3*n+1)]
            self.assertLess(sum(different),0)
            self.assertEqual(sum(different), -Fraction(2,9)*sum(Fraction(1,i) for i in range(n+1,3*n+1)))

    def test_replica_for_arbitrary_nonuniform_weights(self):
        for weights in ((Fraction(1),), (Fraction(1,2),)*9,
                        tuple(Fraction(i,22) for i in range(1,23))):
            total, c, size = sum(weights), min(weights), len(weights)
            for t in (2,3,7):
                R = sum(w**t for w in weights)/total**t
                self.assertLessEqual(Fraction(1,size**(t-1)),R)
                self.assertLessEqual(R,1/(c*size)**(t-1))

    def test_sparse_filter_all_available_levels(self):
        for n in (1,4,30):
            levels = [j**4 for j in range(1,2*n+3)]
            gap = (n+1)**4-n**4
            center = Fraction((n+1)**4+n**4,2)
            minimum = min((s-center)**2/(4*center) for s in levels)
            self.assertEqual(minimum,gap**2/(16*center))


if __name__ == "__main__":
    unittest.main()
