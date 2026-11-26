"""Independent tests of Section 4.4. Uses the Python standard library."""
from fractions import Fraction
import math
import platform


def check_gaussian_source():
    # Product Gaussian integration gives E(exp(-Q_N/x))^2 = prod k/(k+1).
    for n in (1, 8, 32, 256, 4096):
        moment_squared = math.prod(Fraction(k, k + 1) for k in range(1, n + 1))
        assert moment_squared == Fraction(1, n + 1)
        print(f"Gaussian Laplace moment squared, N={n}: {moment_squared}")


def check_walsh_blocks():
    signed_partial = Fraction()
    absolute_partial = Fraction()
    for j in range(1, 5):
        d = 4**j
        signed_count = sum(
            (-1) ** ((a & b).bit_count() % 2)
            for a in range(d) for b in range(d)
        )
        entry_weight = Fraction(1, 2**j * d * math.isqrt(d))
        signed = signed_count * entry_weight
        absolute = d**2 * entry_weight
        assert signed == Fraction(1, 4**j) and absolute == 1
        signed_partial += signed
        absolute_partial += absolute
        print(f"Walsh blocks 1..{j}: signed={signed_partial} absolute={absolute_partial}")


def catalan_from_euler_transform(terms):
    # The positive Euler tail is <= 2**(-terms), since each difference is <= 1.
    differences = [Fraction(1, (2*j + 1)**2) for j in range(terms)]
    total = Fraction()
    for m in range(terms):
        total += differences[0] / 2**(m + 1)
        differences = [a-b for a, b in zip(differences, differences[1:])]
    return total


def check_quarter_turn():
    # 2 C/x**2 = sum (-i)**k/k**2 = -pi**2/48 - i*Catalan, x=pi/4.
    expected = complex(-math.pi**2/48, -float(catalan_from_euler_transform(70)))
    phases = (1+0j, -1j, -1+0j, 1j)
    for n in (64, 256, 1024, 4096):
        terms = [phases[k % 4] / k**2 for k in range(1, n+1)]
        value = complex(math.fsum(z.real for z in terms), math.fsum(z.imag for z in terms))
        bound = math.sqrt(2) / (n+1)**2
        error = abs(expected - value)
        assert error <= bound + 2**-50
        print(f"x=pi/4, N={n}: normalized error={error:.9g} bound={bound:.9g}")


def scaled_kernel(u):
    # (exp(-2iu)-1+2iu)/(2u**2), with cancellation removed near zero.
    if u < 0.1:
        term = -1+0j
        value = term
        for m in range(1, 18):
            term *= -2j*u/(m + 2)
            value += term
        return value
    return complex(-(math.sin(u)/u)**2, (2*u-math.sin(2*u))/(2*u**2))


def integral_by_rational_taylor(lam, order):
    # Integrate the Taylor polynomial of -2*int_0^1 (1-t)*exp(-2iut) dt.
    quarter_turns = ((1, 0), (0, -1), (-1, 0), (0, 1))
    real = Fraction()
    imag = Fraction()
    for m in range(order + 1):
        coeff = -2*lam*(2*lam)**m / (math.factorial(m+2)*(m+1))
        sign_re, sign_im = quarter_turns[m % 4]
        real += coeff*sign_re
        imag += coeff*sign_im
    bound = 2*lam*(2*lam)**(order+1) / (math.factorial(order+3)*(order+2))
    return complex(float(real), float(imag)), float(bound)


def check_joint_scaling():
    # x=lambda/N. The Lipschitz bound |kernel'| <= 2/3 controls the Riemann sum.
    for lam in (Fraction(1, 4), Fraction(1), Fraction(8)):
        reference, taylor_bound = integral_by_rational_taylor(lam, 112)
        print(f"lambda={lam}: integral={reference:.12g} Taylor tail <= {taylor_bound:.3g}")
        for n in (64, 256, 1024, 4096):
            x = float(lam/n)
            terms = [scaled_kernel(k*x) for k in range(1, n+1)]
            scaled = x * complex(math.fsum(z.real for z in terms), math.fsum(z.imag for z in terms))
            error = abs(scaled-reference)
            bound = float(lam**2/(3*n))
            assert error <= bound + taylor_bound + 1e-13
            print(f"  N={n}: error={error:.9g} Riemann bound={bound:.9g}")


if __name__ == "__main__":
    print(f"Python {platform.python_version()}, standard library only")
    check_gaussian_source()
    check_walsh_blocks()
    check_quarter_turn()
    check_joint_scaling()
    print("PASS")
