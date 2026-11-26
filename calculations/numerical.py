"""Deterministic experiments. Each JSON line contains the inputs and outputs of a check."""
import json
from mpmath import mp

from amplitudes import pair_closed, pair_log_sine, pair_partial, pair_tail_integral, small_x, truncation_bound


def emit(experiment, **fields):
    def show(v):
        if isinstance(v, mp.mpc):
            return [mp.nstr(v.real, mp.dps-5), mp.nstr(v.imag, mp.dps-5)]
        if isinstance(v, mp.mpf):
            return mp.nstr(v, mp.dps-5)
        return v
    print(json.dumps({"experiment": experiment, "dps": mp.dps,
                      **{key: show(val) for key, val in fields.items()}}))


def sample_points():
    return [
        ("s=1", mp.mpf(1)), ("s=10", mp.mpf("0.1")), ("s=100", mp.mpf("0.01")),
        ("x=1e-18", mp.mpf("1e-18")), ("x=pi/2", mp.pi/2), ("x=pi", +mp.pi),
        ("x=pi-1e-25", mp.pi-mp.mpf("1e-25")),
        ("x=pi+1e-25", mp.pi+mp.mpf("1e-25")),
        ("x=1e6+1/7", 10**6 + mp.mpf(1)/7),
    ]


def mode_matrix_elements():
    """Create in coordinates, annihilate after rotation in an occupation basis."""
    s = mp.mpf(10)
    for k in (1, 7, 1000):
        v = 1/(2*s*k)
        create = mp.quad(lambda y: v*(y*y-1)**2*mp.exp(-y*y/2)/mp.sqrt(4*mp.pi),
                         [-mp.inf, 0, mp.inf])
        a = mp.matrix(5)
        for n in range(1, 5):
            a[n-1,n] = mp.sqrt(n)
        q = mp.sqrt(v)*(a+a.T)
        u = mp.diag([mp.expj(-n*k/s) for n in range(5)])
        annihilate = (u.H*q*q*u)[0,2]
        expected = mp.sqrt(2)*v
        emit("single_mode_matrix_elements", s=s, k=k, variance=v, create=create,
             rotated_annihilate=annihilate, product=create*annihilate,
             creation_error=abs(create-expected),
             annihilation_error=abs(annihilate-expected*mp.expj(-2*k/s)))
        assert abs(create-expected) < expected*mp.power(10, -(mp.dps-8))
        assert abs(annihilate-expected*mp.expj(-2*k/s)) < expected*mp.power(10, -(mp.dps-8))


def compare_values():
    for label, x in sample_points():
        ref = pair_closed(x)
        quad = pair_log_sine(x)
        relative_scale_error = abs(ref-quad)/x**2
        emit("Li2_vs_log_sine", case=label, x=x, s=1/x, polylog=ref, integral=quad,
             abs_error=abs(ref-quad), error_over_x2=relative_scale_error)
        assert relative_scale_error < mp.power(10, -(mp.dps-15))
        for n in (16, 64, 256, 2048):
            partial = pair_partial(x, n)
            err, bound = abs(ref-partial), truncation_bound(x, n)
            emit("hard_cutoff", case=label, x=x, n=n, partial=partial, abs_error=err, tail_bound=bound)
            assert err <= bound
        if label in {"s=1", "s=10", "x=pi", "x=pi+1e-25", "x=1e-18"}:
            n = 12
            total = pair_partial(x, n) + pair_tail_integral(x, n)
            err = abs(ref-total)/x**2
            emit("direct_prefix_plus_Laplace_tail", case=label, x=x, n=n, result=total, error_over_x2=err)
            assert err < mp.power(10, -(mp.dps-15))


def regulators():
    for x in (mp.mpf("0.1"), +mp.pi):
        for n in (16, 256, 4096):
            # eps = 1/n. Match the UV scale, not the detailed cutoff profile.
            eps = 1/mp.mpf(n)
            exact = pair_closed(x)
            abel = x**2/2*mp.polylog(2, mp.exp(-eps-2j*x))
            fejer = x**2/2*mp.fsum((1-mp.mpf(k)/(n+1))*mp.expj(-2*k*x)/k**2
                                     for k in range(1, n+1))
            h = mp.harmonic(n)
            # 1-exp(-eps*k) <= eps*k for k <= n; beyond n use the absolute tail.
            abel_bound = x**2/2*(eps*h+1/mp.mpf(n))
            fejer_bound = x**2/2*(h/(n+1)+1/mp.mpf(n))
            emit("regulators", x=x, n=n, eps=eps, abel=abel, fejer=fejer,
                 abel_error=abs(abel-exact), fejer_error=abs(fejer-exact),
                 abel_bound=abel_bound, fejer_bound=fejer_bound,
                 cubic_over_minus_i_hard=h, cubic_over_minus_i_abel=-mp.log(-mp.expm1(-eps)),
                 cubic_over_minus_i_fejer=h-mp.mpf(n)/(n+1))
            assert abs(abel-exact) < abel_bound and abs(fejer-exact) < fejer_bound


def asymptotics():
    for x in map(mp.mpf, ("0.5", "0.01", "0.0001", "1e-8")):
        for order in (0, 1, 2):
            approx, bound = small_x(x, order)
            error = abs(approx-pair_closed(x))
            emit("asymptotic_remainder", x=x, order=order, approximation=approx,
                 abs_error=error, bound=bound)
            assert error <= bound
    for n in (16, 256, 4096):
        h, h2 = mp.harmonic(n), mp.fsum(1/mp.mpf(k)**2 for k in range(1, n+1))
        emit("uncentered_source_and_generator", n=n, x=mp.mpf(1), raw_mean=h/2,
             centered_norm_squared=h2/2, pair_K_form=h)


if __name__ == "__main__":
    for precision in (85, 125):
        mp.dps = precision
        mode_matrix_elements()
        compare_values()
    regulators()
    asymptotics()
