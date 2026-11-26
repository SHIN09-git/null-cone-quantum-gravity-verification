"""Checks with independent matrix, integral, special-value and cutoff oracles."""
import sys
import unittest
from pathlib import Path
from mpmath import mp
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/"calculations"))
from amplitudes import pair_closed, pair_log_sine, pair_partial, pair_tail_integral, small_x, truncation_bound


class OscillatorTests(unittest.TestCase):
    def test_gaussian_coordinate_creation_and_annihilation(self):
        with mp.workdps(65):
            for v in map(mp.mpf, ("0.5", "0.01", "3.7")):
                # Rescale q = sqrt(v)*y so the quadrature is standard normal.
                def integrand(y):
                    return mp.exp(-y*y/2)*v*(y*y-1)**2/mp.sqrt(4*mp.pi)
                creation = mp.quad(integrand, [-mp.inf, 0, mp.inf])
                self.assertLess(abs(creation - mp.sqrt(2)*v), mp.mpf("1e-60"))
                t = mp.mpf("0.31")
                a = mp.matrix(4)
                for n in range(1, 4):
                    a[n-1, n] = mp.sqrt(n)
                q = mp.sqrt(v)*(a + a.T)
                u = mp.diag([mp.expj(-n*t) for n in range(4)])
                annihilation = (u.H*q*q*u)[0, 2]
                self.assertLess(abs(annihilation - mp.expj(-2*t)*creation), mp.mpf("1e-60"))

    def test_two_independent_modes_connected_subtraction(self):
        a = sp.Matrix([[0, 1, 0], [0, 0, sp.sqrt(2)], [0, 0, 0]])
        q2 = (a+a.T)**2
        q_one = sp.kronecker_product(q2, sp.eye(3))
        q_two = sp.kronecker_product(sp.eye(3), q2)
        u = sp.kronecker_product(sp.diag(1, -sp.I, -1), sp.diag(1, -1, 1))
        mixed = (u.H*q_one*u*q_two)[0, 0] - q_one[0, 0]*q_two[0, 0]
        self.assertEqual(mixed, 0)
        all_q = q_one + sp.Rational(1, 2)*q_two
        self.assertEqual((u.H*all_q*u*all_q)[0, 0] - all_q[0, 0]**2, -sp.Rational(3, 2))

    def test_generator_form_and_raw_source(self):
        k = sp.Symbol("k", integer=True, positive=True)
        v = 1/(2*k)
        self.assertEqual(sp.simplify(2*k*2*v**2), 1/k)
        self.assertEqual(sp.summation(2*v**2, (k, 1, sp.oo)), sp.pi**2/12)
        self.assertEqual(sp.summation(v, (k, 1, sp.oo)), sp.oo)
        self.assertEqual(sp.summation(k*2*v**2, (k, 1, sp.oo)), sp.oo)

    def test_uncentered_laplace_transform(self):
        k, n = sp.symbols("k n", integer=True, positive=True)
        t = sp.symbols("t", real=True)
        mode = sp.integrate(sp.exp(-t**2/(2*k))*sp.exp(-t**2/2)/sp.sqrt(2*sp.pi),
                            (t, -sp.oo, sp.oo))
        self.assertEqual(sp.simplify(mode**2-k/(k+1)), 0)
        self.assertEqual(sp.simplify(sp.product(k/(k+1), (k,1,n)) - 1/(n+1)), 0)


class CutTests(unittest.TestCase):
    def test_single_cut_and_cauchy_schwarz(self):
        u = sp.Matrix([[1, sp.I], [sp.I, 1]])/sp.sqrt(2)
        v = sp.Matrix([[3, -4], [4, 3]])/5
        a, b = sp.Matrix([1, 2*sp.I]), sp.Matrix([2-sp.I, 1])
        terms = [(b.H*v)[i]*(u*a)[i] for i in range(2)]
        self.assertEqual(sp.simplify((b.H*v*u*a)[0]-sum(terms)), 0)
        self.assertTrue(sum(abs(t) for t in terms) <= a.norm()*b.norm())

    def test_independent_projections_multicut_bound(self):
        u = sp.Matrix([[3,-4,0], [4,3,0], [0,0,5]])/5
        v = sp.Matrix([[5,0,0], [0,3,-4], [0,4,3]])/5
        a, b = sp.Matrix([2, 3, -1]), sp.Matrix([1, -1, 2])
        p = sp.diag(0,1,1)
        g = sp.Matrix([2,1,0])
        q = g*g.T / g.dot(g)
        error = abs((b.H*(u*v*u - u*q*v*p*u)*a)[0])
        bound = b.norm()*(((sp.eye(3)-p)*u*a).norm()+((sp.eye(3)-q)*v*u*a).norm())
        self.assertGreater(error, 0)
        self.assertTrue(error <= bound)


class SeriesTests(unittest.TestCase):
    def test_resonance_half_and_quarter_turn(self):
        with mp.workdps(85):
            for x, f in [(mp.pi, mp.zeta(2)), (mp.pi/2, -mp.zeta(2)/2),
                         (mp.pi/4, mp.mpc(-mp.pi**2/48, -mp.catalan))]:
                for calc in (pair_closed, pair_log_sine):
                    self.assertLess(abs(2*calc(x)/x**2-f), mp.mpf("1e-78"))

    def test_truncation_at_and_near_resonance(self):
        with mp.workdps(65):
            for n in (1, 9, 128):
                exact = mp.pi**2*mp.polygamma(1, n+1)/2
                self.assertLess(abs(abs(pair_closed(mp.pi)-pair_partial(mp.pi,n))-exact), mp.mpf("1e-60"))
                for x in (mp.mpf("0.03"), mp.mpf("0.8"), mp.pi+mp.mpf("1e-18")):
                    tail = pair_tail_integral(x,n)
                    self.assertLess(abs(tail), truncation_bound(x,n))
                    self.assertLess(abs(pair_partial(x,n)+tail-pair_closed(x)), mp.mpf("1e-57"))

    def test_asymptotic_branch_and_remainder(self):
        with mp.workdps(95):
            for x in map(mp.mpf, ("0.23", "0.001")):
                exact = pair_partial(x,10) + pair_tail_integral(x,10)
                approx, bound = small_x(x, 2)
                self.assertLess(abs(approx-exact), bound)
                explicit_im = x**3*(mp.log(2*x)-1) - x**5/18 - x**7/900
                self.assertLess(abs(approx.imag-explicit_im), mp.mpf("1e-90"))
            x = mp.mpf("1e-6")
            finite_n = (pair_partial(x,20).real - x**2*mp.fsum(1/mp.mpf(k)**2 for k in range(1,21))/2)/x**3
            infinite_n = (pair_log_sine(x).real - x**2*mp.pi**2/12)/x**3
            self.assertLess(abs(finite_n), 21*x)
            self.assertLess(abs(infinite_n+mp.pi/2), x)

    def test_distinct_regulators_at_fixed_mode_count(self):
        with mp.workdps(55):
            n = 19
            eps = mp.mpf("0.2")
            hard = mp.fsum(1/mp.mpf(k) for k in range(1,n+1))
            fejer = mp.fsum((1-mp.mpf(k)/(n+1))/k for k in range(1,n+1))
            self.assertLess(abs(hard-fejer-mp.mpf(n)/(n+1)), mp.mpf("1e-50"))
            abel = mp.nsum(lambda k: mp.exp(-eps*k)/k, [1,mp.inf])
            self.assertLess(abs(abel+mp.log(1-mp.exp(-eps))), mp.mpf("1e-50"))


if __name__ == "__main__":
    unittest.main()
