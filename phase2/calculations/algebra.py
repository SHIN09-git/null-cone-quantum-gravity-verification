"""Symbolic finite-cut identities used in the audit of section 5.2."""
import sympy as sp


def vec(matrix):
    """Coefficients in |out i> ⊗ |conjugate in j>, with i first."""
    return sp.Matrix([matrix[i, j] for i in range(matrix.rows) for j in range(matrix.cols)])


def check(label, difference):
    result = sp.simplify(sp.expand_complex(difference))
    assert result == 0, (label, result)
    print(label, "= 0")


def main():
    a, b = sp.symbols("a b", positive=True)
    phase = sp.symbols("theta", real=True)
    k = sp.symbols("k", positive=True)
    c = sp.diag(sp.sqrt(a), sp.sqrt(b))
    sx = sp.Matrix([[0, 1], [1, 0]])
    observable = -sp.kronecker_product(sx, sx)
    basis = sp.eye(2)
    right_boost = sp.kronecker_product(basis, sp.diag(1, sp.exp(sp.I*phase)))
    delta_op = right_boost.H * observable * right_boost - observable
    pair = vec(c)
    kernel = 2*sp.sqrt(a*b)*(1-sp.cos(phase))
    check("paired squared norm minus Tr W", pair.dot(pair) - sp.trace(c.H*c))
    check("two-level boosted numerator minus K", (pair.H*delta_op*pair)[0] - kernel)
    p, q = sp.diag(1, 0), sp.diag(0, 1)
    for proj in (p, q):
        v = vec(c*proj)
        check("isolated diagonal preparation has zero response", (v.H*delta_op*v)[0])
    # An actual complex projection need not commute with the area weights.
    p_complex = sp.Matrix([[1, -sp.I], [sp.I, 1]])/2
    A = c*p_complex
    vector = vec(A)
    test_area = sp.diag(2, 5)
    rhs = sp.trace(p_complex*c.H*c*p_complex*test_area)
    check("right marginal on noncommuting projection",
          (vector.H*sp.kronecker_product(basis, test_area.T)*vector)[0]-rhs)
    test_right = sp.Matrix([[1, sp.I], [-sp.I, 3]])
    check("right transpose for complex test observable",
          (vector.H*sp.kronecker_product(basis, test_right.T)*vector)[0]
          - sp.trace(A.H*A*test_right))
    signed = kernel - (k*a+b)*kernel/(2*(a+b))
    check("signed numerator for k inside per one outside",
          signed-kernel*((2-k)*a+b)/(2*(a+b)))

    tau, x = sp.symbols("tau x", positive=True)
    # Laplace integral of exp(-tau*omega) exp(i*x*omega), then one derivative.
    abel_kernel = sp.re(-sp.diff(1/(tau-sp.I*x), tau))
    check("Abel kernel at separated points",
          abel_kernel-(tau**2-x**2)/(tau**2+x**2)**2)
    check("off-diagonal coincidence regulator removed", sp.limit(abel_kernel,tau,0)+1/x**2)
    z = sp.symbols("exp_eta", positive=True)
    check("vacuum boost fraction", 1-4*z/(1+z)**2-((z-1)/(z+1))**2)
    eps = sp.symbols("eps", positive=True)
    weighted_trace = a/(sp.exp(2*eps/k)-1)+b/(sp.exp(2*eps)-1)
    cross_sum = kernel/(sp.exp((1+1/k)*eps)-1)
    check("smooth cutoff normalized limit",
          sp.limit(cross_sum/weighted_trace,eps,0,dir="+")-2*k*kernel/((k+1)*(k*a+b)))
    print("all symbolic checks passed")


if __name__ == "__main__":
    main()
