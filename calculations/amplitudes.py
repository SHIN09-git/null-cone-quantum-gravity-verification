"""Scalar amplitude of Eq. (4.33). The independent variable is x = 1/s."""
from mpmath import mp


def pair_partial(x, n):
    """Hard radial cutoff. Evaluate the complex exponential separately for each k."""
    return x**2 / 2 * mp.fsum(mp.expj(-2*k*x) / k**2 for k in range(1, n + 1))


def pair_closed(x):
    return x**2 / 2 * mp.polylog(2, mp.expj(-2*x))


def truncation_bound(x, n):
    """Integral-test bound, optionally sharpened by geometric cancellation."""
    absolute = 1 / mp.mpf(n)
    sine = abs(mp.sin(x))
    if sine:
        absolute = min(absolute, 1 / (sine * (n + 1)**2))
    return x**2 / 2 * absolute


def pair_log_sine(x):
    """Real Fourier polynomial and a real quadrature with the endpoint log removed."""
    theta = 2 * (x - mp.pi * mp.nint(x / mp.pi))
    a = abs(theta)
    real_part = mp.pi**2 / 6 - mp.pi*a/2 + a**2/4
    if not a:
        return x**2 * real_part / 2
    smooth = mp.quad(lambda t: mp.log(mp.sinc(a*t/2)), [0, 1])
    imag_part = theta * (mp.log(a) - 1 + smooth)
    return x**2 / 2 * mp.mpc(real_part, imag_part)


def pair_tail_integral(x, n):
    """Exact tail as a Laplace integral. Does not call polylog or log-sine."""
    theta = 2 * (x - mp.pi * mp.nint(x / mp.pi))
    m = n + 1

    def integrand(y):
        if y == 0:
            return m if theta == 0 else mp.zero
        return y * mp.exp(-y) / (-mp.expm1(-y/m - 1j*theta))

    # Resolve the narrow layer at y ~ m*abs(theta) for near-resonant tests.
    scale = m * abs(theta)
    knots = [mp.zero]
    if 0 < scale < 1:
        while scale < 1:
            knots.append(scale)
            scale *= 100
    knots.extend([1, mp.inf])
    return x**2 / 2 * mp.expj(-m*theta) / m**2 * mp.quad(integrand, knots)


def small_x(x, order):
    """Keep order terms of log(sin(t)/t) beyond its leading logarithm."""
    if not 0 < x < mp.pi or order < 0:
        raise ValueError("requires 0 < x < pi and a nonnegative order")
    r = x / mp.pi
    re = x**2 * (mp.pi**2/6 - mp.pi*x + x**2) / 2
    corr = mp.fsum(mp.zeta(2*j)*r**(2*j)/(j*(2*j+1)) for j in range(1, order+1))
    approx = mp.mpc(re, x**3 * (mp.log(2*x) - 1 - corr))
    bound = x**3 * mp.zeta(2)*r**(2*order+2) / ((order+1)*(2*order+3)*(1-r**2))
    return approx, bound
