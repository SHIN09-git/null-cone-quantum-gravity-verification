"""Independent finite matrix checks. Infinite-dimensional assertions are proved in the report."""
import itertools
import math
import unittest
from fractions import Fraction
import sympy as sp


def tensor_vector(matrix):
    return sp.Matrix(list(matrix))


class ClosureTests(unittest.TestCase):
    def test_open_projection_and_closed_tail(self):
        # x_n=y_n=2^{-n/2}, n starts at 1, so the exact open tail is 2^{-N}.
        for size in (1, 3, 17, 112):
            open_sum = sum(Fraction(1, 2**n) for n in range(1, size+1))
            self.assertEqual(1-open_sum, Fraction(1, 2**size))
            self.assertEqual(sum(1 for _ in range(size)), size)

    def test_disjoint_projections_have_cross_terms(self):
        # A product of anticommuting-with-the-boost flips, on distinct tensor legs.
        sx = sp.Matrix([[0, 1], [1, 0]])
        insertion = sp.kronecker_product(sx, sx)
        vectors = [tensor_vector(sp.diag(1, 0)), tensor_vector(sp.diag(0, 1))]
        self.assertTrue(all((v.H*insertion*v)[0] == 0 for v in vectors))
        v = vectors[0]+vectors[1]
        self.assertEqual((v.H*insertion*v)[0], 2)

    def test_noncommuting_cut_marginal_and_distance(self):
        # C also maps to a cap with a genuinely different dimension.
        c = sp.Matrix([[sp.I/2, 0], [0, sp.Rational(2, 3)], [sp.Rational(1, 2), 0]])
        z = sp.Matrix([1, sp.I])/sp.sqrt(2)
        p = z*z.H
        s = sp.diag(1, 4)
        self.assertNotEqual(p*s, s*p)
        v = tensor_vector(c*p)
        mass = sp.trace(p*c.H*c)
        self.assertEqual((v.H*v)[0], mass)
        current = sp.kronecker_product(sp.eye(3), s.T**2)
        self.assertEqual((v.H*current*v)[0], sp.trace(p*c.H*c*p*s**2))
        # |exp(ix)-1|^2 on the two components, calculated separately.
        for eta in (-2.0, 0.0, 1e-9, 1.7):
            angle = eta/(2*math.pi)
            distances = sp.diag(*(4*math.sin(angle*x/2)**2 for x in (1,4)))
            lhs = float(sp.re((v.H*sp.kronecker_product(sp.eye(3),distances)*v)[0]/mass))
            rhs = angle**2*float(sp.trace(p*c.H*c*p*s**2)/mass)
            self.assertLessEqual(lhs, rhs+1e-26)

    def test_cycles_not_only_initial_intervals(self):
        # An outside vector b_j and inside a_j contribute only when both appear.
        k = 8
        ratio = Fraction(1, 4)
        balanced = 1/(1+ratio)  # responses in units of the cross-term kernel
        for count in range(1, 5):
            for indices in itertools.combinations(range(1, 10), count):
                inside = {k*(j-1)+h for j in indices for h in range(1, k+1)}
                matched = len(inside.intersection(indices))
                self.assertLessEqual(Fraction(matched)/(count*(k+ratio)), balanced/2)

    def test_basis_independent_vectorization(self):
        c = sp.Matrix([[1,sp.I], [0,2]])
        unitary = sp.Matrix([[1,sp.I],[sp.I,1]])/sp.sqrt(2)
        total = sp.zeros(4,1)
        for j in range(2):
            e = unitary[:,j]
            total += sp.kronecker_product(c*e,e.conjugate())
        self.assertEqual(sp.simplify(total-tensor_vector(c)), sp.zeros(4,1))

    def test_finite_dimensional_partition_function(self):
        q = sp.Rational(1,7)   # test e^{-s} with a fourfold degeneracy
        w = sp.diag(q,q,q,q,1)
        rho = w/sp.trace(w)
        self.assertEqual(sp.trace(rho), 1)
        self.assertEqual(sp.trace(w)*sp.trace(rho*w.inv()), 5)

    def test_compact_spectrum_can_have_infinite_multiplicity(self):
        # Exact finite blocks inside the two infinite area eigenspaces.
        for n in (1,5,103):
            weights = [Fraction(1,4)]*(2*n) + [Fraction(1,8)]*n
            self.assertGreaterEqual(sum(weights), len(weights)*min(weights))
            replica = sum(w*w for w in weights)/sum(weights)**2
            self.assertEqual(replica, Fraction(9,25*n))

    def test_multiplication_operator_on_dyadic_cells(self):
        # W(s)=(1+s)/2 on [0,1]. The mean on each cell is its midpoint value.
        for m in (1, 3, 9):
            count = 2**m
            diagonal = [(1+Fraction(2*j+1,2*count))/2 for j in range(count)]
            self.assertEqual(sum(diagonal), count*Fraction(3,4))

    def test_finite_norm_alternative_if_the_lower_bound_is_removed(self):
        for n in (4, 17, 113):
            weights = [Fraction(1, 2**j) for j in range(1,n+1)]
            self.assertEqual(sum(weights), 1-Fraction(1,2**n))
            self.assertLess(min(weights), Fraction(2,n))


if __name__ == "__main__":
    unittest.main()
