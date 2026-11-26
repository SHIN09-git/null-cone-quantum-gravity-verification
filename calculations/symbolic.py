"""Independent coordinate-space and number-basis checks. Prints exact relations."""
import sympy as sp


def main():
    q = sp.Symbol("q", real=True)
    v = sp.Symbol("v", positive=True)  # v = (Delta q)^2
    density = sp.exp(-q**2/(2*v)) / sp.sqrt(2*sp.pi*v)
    h2 = (q**2/v - 1)/sp.sqrt(2)
    ex = lambda f: sp.simplify(sp.integrate(f*density, (q, -sp.oo, sp.oo)))
    moments = [ex(f) for f in [1, q**2, q**4, h2, h2**2, h2*(q**2-v)]]
    assert moments == [1, v, 3*v**2, 0, 1, sp.sqrt(2)*v]
    print("Gaussian norms, moments, and vacuum->pair:", moments)

    # Starting on |0>, two quadratic insertions visit at most level 4.
    a = sp.zeros(5)
    for n in range(1, 5):
        a[n-1, n] = sp.sqrt(n)
    q2 = v*(a + a.T)**2
    t = sp.Symbol("t", real=True)
    rotation = sp.diag(*(sp.exp(-sp.I*t*n) for n in range(5)))
    connected = sp.simplify((rotation.H*q2*rotation*q2)[0, 0] - q2[0, 0]**2)
    assert connected == 2*v**2*sp.exp(-2*sp.I*t)
    print("Connected conjugated operator matrix element:", connected)

    x = sp.Symbol("x", real=True)
    k = sp.Symbol("k", integer=True, positive=True)
    summand = x**2 * sp.exp(-2*sp.I*k*x) / (2*k**2)
    cubic = sp.simplify(sp.diff(summand, x, 3).subs(x, 0)/sp.factorial(3))
    assert cubic == -sp.I/k
    print("Finite-cutoff cubic coefficient per mode, x=1/s:", cubic)
    log_sinc = sp.series(sp.log(sp.sin(x)/x), x, 0, 8)
    print("Regular kernel in exact log-sine integral:", log_sinc)
    assert log_sinc.removeO().expand().coeff(x, 2) == -sp.Rational(1, 6)
    assert log_sinc.removeO().expand().coeff(x, 4) == -sp.Rational(1, 180)
    print("PASS")


if __name__ == "__main__":
    main()
