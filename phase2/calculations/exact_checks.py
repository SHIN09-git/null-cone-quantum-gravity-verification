"""Independent finite algebra for the operator, thermal and clock tests in this reappraisal."""
from fractions import Fraction
import sympy as sp


def pair_contraction():
    w, delta = sp.symbols("w delta", positive=True)
    theta = sp.symbols("theta", real=True)
    flip = sp.Matrix([[0,1],[1,0]])
    op = -sp.kronecker_product(flip,flip)
    boost = sp.kronecker_product(sp.eye(2),sp.diag(1,sp.exp(sp.I*theta)))
    v = sp.sqrt(w)*sp.Matrix([1,0,0,1])
    numerator = sp.simplify(sp.expand_complex((v.H*(boost.H*op*boost-op)*v)[0]))
    assert sp.simplify(numerator-2*w*(1-sp.cos(theta))) == 0
    n,r = sp.symbols("n r", positive=True, integer=True)
    signed = 2*n*w*delta - w*(r+n)*delta/2
    for name, inside, expected in (("paired",n,n),("biased",7*n,-2*n),
                                   ("finite positive",3*n-2,1),("zero",3*n,0),
                                   ("finite negative",3*n+2,-1)):
        assert sp.simplify(signed.subs(r,inside) - expected*w*delta) == 0
        print("hard cutoff",name,"Z/(w delta) =",expected)
    # In (5.25) the two areas 1 and 3 have exactly the same effective weight.
    assert sp.simplify(sp.exp(-1-(1-3)**2/sp.Integer(2))-sp.exp(-3)) == 0
    # Recover the general variance estimate from a rotating, non-area-eigenbasis cut.
    z = sp.Matrix([1,2*sp.I,1])/sp.sqrt(6)
    P = sp.eye(3)-z*z.H
    W = sp.diag(sp.Rational(1,4),sp.Rational(1,9),sp.Rational(1,16))
    s = sp.diag(1,2,4)
    C = W.applyfunc(sp.sqrt)
    M = C*P
    V = sp.Matrix(list(M))
    trace = sp.trace(P*W)
    assert P*s != s*P
    assert (V.H*V)[0] == trace
    moments = (V.H*sp.kronecker_product(sp.eye(3),(s-2*sp.eye(3)).T**2)*V)[0]
    assert moments == sp.trace(P*W*P*(s-2*sp.eye(3))**2)
    print("noncommuting finite projection norm",trace,"right second moment numerator",moments)


def replica_and_thermal():
    p,Z = sp.symbols("p Z", positive=True)
    # On the finite diamond the two signs have equal total mass p(1-p).
    pos = p*(1-p)
    neg = -(1-p)*p
    assert sp.simplify(pos+neg) == 0
    assert sp.simplify((pos-neg)*Z-2*p*(1-p)*Z) == 0
    print("absolute weight over rectangular joint cut = 2 p(1-p) Z")
    for n in (1,4,16,64):
        # Nonconstant positive W on a continuous band, exactly integrated using rationals.
        cell_means = [Fraction(1,2)+Fraction(2*j+1,4*n) for j in range(n)]
        total = sum(cell_means)
        ratio = sum(x*x for x in cell_means)/total**2
        assert total == n*Fraction(3,4)
        assert n*ratio == Fraction(28,27)-Fraction(1,27*n**2)
        print("dyadic n",n,"rank times R_2",n*ratio)
    q = sp.Rational(257,302)
    assert q/(2*(1-q))-sp.Rational(1,2) == sp.Rational(106,45)
    print("Schwarzschild (5.68) into (5.69):",q/(2*(1-q))-sp.Rational(1,2))
    alpha, s, lam = sp.symbols("alpha s lam", real=True)
    assert -sp.diff(alpha**-sp.Rational(1,2),alpha).subs(alpha,1) == sp.Rational(1,2)
    # M(lam) is the moment generating function of the window center at fixed true area.
    log_mgf = -sp.log(1-4*lam)/2+s*(1-sp.sqrt(1-4*lam))/2
    mean = sp.diff(log_mgf,lam).subs(lam,0)
    variance = sp.diff(log_mgf,lam,2).subs(lam,0)
    assert sp.simplify(variance+(mean-s)**2) == 2*s+12
    print("full weighted filter cost 1/2; conditional squared center displacement",2*s+12)


def clock_uncertainty():
    # Gaussian Cauchy–Schwarz on the real axis of the Bargmann transform.
    x,t = sp.symbols("x t", real=True)
    exponent = -4*x**2+2*sp.sqrt(2)*t*x
    assert sp.expand(exponent + 4*(x-t/(2*sp.sqrt(2)))**2 - t**2/2) == 0
    angular_bound = -sp.Rational(1,4)+sp.Rational(3,4)*sp.sin(sp.pi/6)**2
    assert angular_bound == -sp.Rational(1,16)
    print("three-axis Bargmann growth bound",angular_bound,"times |z|^2")
    v, epsilon = sp.symbols("v epsilon", real=True, positive=True)
    k = sp.symbols("k", integer=True, positive=True)
    # Orthogonality is on [0,pi] after changing the radial coordinate.
    assert sp.integrate(sp.cos(k*v)**2,(v,0,sp.pi)) == sp.pi/2
    print("Dirichlet-cosine diagonal norm pi/2; focusing lower factor",
          epsilon*sp.pi**2/(8*(1-epsilon)))


if __name__ == "__main__":
    pair_contraction()
    replica_and_thermal()
    clock_uncertainty()
    print("PASS")
