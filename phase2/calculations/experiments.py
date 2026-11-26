"""High-precision projections and smooth regulators for a two-area Hilbert space."""
import json
from mpmath import mp


def record(name, **fields):
    row = {"case": name, "dps": mp.dps}
    for key, value in fields.items():
        row[key] = value if isinstance(value, int) else mp.nstr(value, 65)
    print(json.dumps(row, sort_keys=True, ensure_ascii=False))


def hard_cut(s_center, inside, outside, eta=1):
    """Apply the product of the two flips directly on the diagonal tensor vectors."""
    s = mp.mpf(s_center)
    weights = [mp.exp(-s), mp.exp(-(s+1)-mp.mpf("0.5"))]
    coefficients = {}
    for level, count in enumerate((inside, outside)):
        for index in range(1, count+1):
            coefficients[index, level] = mp.sqrt(weights[level])
    norm = mp.fsum(abs(value)**2 for value in coefficients.values())

    def expectation(angle):
        boosted = {key: value*mp.expj(angle*(s+key[1])/(2*mp.pi))
                   for key, value in coefficients.items()}
        return -mp.re(mp.fsum(value.conjugate()*boosted.get((i, 1-level), 0)
                              for (i, level), value in boosted.items()))
    change = expectation(eta)-expectation(0)
    return norm, change


def relative_constants():
    ratio = mp.exp(-mp.mpf(3)/2)
    kernel = 4*mp.sqrt(ratio)*mp.sin(1/(4*mp.pi))**2
    return ratio, kernel


def smooth_cut(eps, k, ratio, kernel):
    # Values divided by exp(-S); both sums start at index 1.
    norm = 1/mp.expm1(2*eps/k) + ratio/mp.expm1(2*eps)
    numerator = kernel/mp.expm1((1+mp.mpf(1)/k)*eps)
    return norm, numerator


def run():
    for digits in (80, 130):
        with mp.workdps(digits):
            u, kernel = relative_constants()
            delta = kernel/(1+u)
            for center in (10_000, 100_000_000):
                # At the larger center, the independent phase evaluation loses up
                # to 9 digits through the removable overall phase.
                weight = mp.exp(-center)
                for k in (1, 8):
                    for n in (1, 17, 64):
                        norm, change = hard_cut(center, k*n, n)
                        ratio = change/norm
                        signed = (change-delta*norm/2)/(weight*n)
                        expected = kernel/(k+u)
                        assert abs(ratio-expected) < mp.power(10, -digits+14)
                        assert mp.almosteq(norm/weight, n*(k+u))
                        assert (signed > 0) == (k == 1)
                        record("hard", S=center, k=k, n=n, trace_over_exp_minus_S=norm/weight,
                               response=ratio, signed_per_block_over_exp_minus_S=signed,
                               difference_from_formula=abs(ratio-expected))
            for k in (1, 8):
                limit = 2*k*kernel/((k+1)*(k+u))
                for eps in map(mp.mpf, ("0.25","0.01","1e-8","1e-30")):
                    norm, numerator = smooth_cut(eps, k, u, kernel)
                    response = numerator/norm
                    record("smooth", k=k, eps=eps, eps_times_scaled_trace=eps*norm,
                           response=response, limit=limit, absolute_error=abs(response-limit))
                # Independently sum the smooth regulator at a finite upper endpoint.
                eps = mp.mpf("0.25")
                n_max = 2304
                norm = mp.fsum(mp.exp(-2*eps*i/k)+u*mp.exp(-2*eps*i)
                               for i in range(1,n_max+1))
                numerator = kernel*mp.fsum(mp.exp(-(1+mp.mpf(1)/k)*eps*i)
                                           for i in range(1,n_max+1))
                full_norm, full_num = smooth_cut(eps,k,u,kernel)
                tail = (mp.exp(-2*eps*n_max/k)/mp.expm1(2*eps/k)
                        +u*mp.exp(-2*eps*n_max)/mp.expm1(2*eps))
                num_tail = kernel*mp.exp(-(1+mp.mpf(1)/k)*eps*n_max)/mp.expm1((1+mp.mpf(1)/k)*eps)
                assert mp.almosteq(norm+tail, full_norm)
                assert mp.almosteq(numerator+num_tail, full_num)
                record("geometric_tail", k=k, n=n_max, eps=eps, scaled_trace_tail=tail,
                       scaled_numerator_tail=num_tail)
            for eta in map(mp.mpf, ("-1","1e-12","1","4")):
                z = mp.exp(eta)
                loss = 1-4*z/(1+z)**2
                assert abs(loss-mp.tanh(eta/2)**2) < mp.eps*4
                record("free_shear", eta=eta, fractional_loss=loss,
                       small_eta_coefficient=loss/eta**2)


if __name__ == "__main__":
    run()
