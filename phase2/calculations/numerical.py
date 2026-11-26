"""High-precision independent tests. Each JSON row is a measured value or a rigorous bound."""
import json
from mpmath import mp


def row(case, **values):
    out = {"case": case, "dps": mp.dps}
    for key, value in values.items():
        out[key] = value if isinstance(value, int) else mp.nstr(value, 60)
    print(json.dumps(out, ensure_ascii=False))


def replica():
    weight = lambda x: mp.exp(-x-x*x/2)
    primitive = lambda x: mp.sqrt(mp.pi/2)*mp.exp(mp.mpf("0.5"))*mp.erf((1+x)/mp.sqrt(2))
    I = mp.quad(weight, [0,1])
    J = mp.quad(lambda x: weight(x)**2, [0,1])
    disk = mp.quad(lambda x: mp.exp(-2-x)*weight(x)**2, [0,1])/I**2
    assert disk >= 1/(mp.exp(3)-mp.exp(2))
    for N in (2,8,32,128):
        bins = [mp.mpf(j)/N for j in range(N+1)]
        means = [N*(primitive(b)-primitive(a)) for a,b in zip(bins[:-1],bins[1:],strict=True)]
        tr = mp.fsum(means)
        R = mp.fsum(x*x for x in means)/tr**2
        assert mp.almosteq(tr,N*I)
        err = J/I**2-N*R
        assert 0 <= err <= 1/(12*N*N*I**2)
        row("replica", N=N, trace_rescaled=tr, exact_compression_R=R, rank_times_R=N*R,
            limiting_rank_times_R=J/I**2, error=err, proved_error_bound=1/(12*N*N*I**2),
            regular_disk_ratio=disk)


def ads():
    p = mp.mpf(2)/3
    for n in (8,128,2048,32768):
        harmonic = mp.harmonic(n)
        k = 3
        tail = mp.harmonic(k*n)-harmonic
        near = -p*(1-p)*tail
        far = -p*(1-p)*(mp.harmonic(n*n)-harmonic)
        target = -p*(1-p)*mp.log(k)
        assert 0 <= near-target <= p*(1-p)*(k-1)/(k*n)
        assert far < near
        row("joint", n=n, rectangular=0, absolute_rectangular=2*p*(1-p)*harmonic,
            through_3n=near, through_3n_limit=target, through_n_squared=far)


def horizon():
    density = lambda x: 4*x/mp.sinh(mp.pi*x) if x else 4/mp.pi
    edges = [0,1,2,4,8,16,32,64,128]
    K, steps, T = 6, 96, 2
    h = mp.mpf(K)/steps
    masses, centers = [], []
    for j in range(steps):
        iv = [j*h,(j+1)*h]
        mass = mp.quad(density, iv)
        masses.append(mass)
        centers.append(mp.quad(lambda x: x*density(x), iv)/mass)
    tail = 1-mp.fsum(masses)
    assert 0 < tail <= 8*mp.exp(-mp.pi*K)*(K/mp.pi+1/mp.pi**2)/(1-mp.exp(-2*mp.pi*K))
    centers.append(mp.mpf(K))
    masses.append(tail)
    uniform_bound = T*T*h*h/8+16*mp.exp(-mp.pi*K)*(K/mp.pi+1/mp.pi**2)/(1-mp.exp(-2*mp.pi*K))
    for eta in map(mp.mpf, ("0","0.2","0.5","1","1.5","2")):
        exact = 1/mp.cosh(eta/2)**2
        integral = mp.quad(lambda x: density(x)*mp.cos(eta*x), edges)
        discrete = mp.fsum(p*mp.cos(eta*x) for p,x in zip(masses,centers,strict=True))
        direct_error, finite_error = abs(integral-exact), abs(discrete-exact)
        assert direct_error < mp.mpf(10)**(-mp.dps+6)
        assert finite_error <= uniform_bound
        row("horizon", eta=eta, proper_ratio=exact, fourier_integral=integral,
            quadrature_difference=direct_error, discrete_response=discrete,
            approximation_error=finite_error, uniform_bound=uniform_bound, atoms=len(masses))


def sparse():
    gamma = mp.mpf(257)/90
    for n in (8,32,128,512):
        # Rounding m_n up adds less than exp(-n^4) to the n-th thermal weight.
        s = n**4
        gap = (n+1)**4-s
        center = mp.mpf(s)+mp.mpf(gap)/2
        q = mp.fsum(j**2*(mp.mpf(j)**(4*gamma)-mp.mpf(j-1)**(4*gamma))
                    for j in range(1,n+1))/(n**2*mp.mpf(n)**(4*gamma))
        gap_cost = gap**2/(16*center)
        row("sparse", n=n, q_without_integer_rounding=q, q_limit=2*gamma/(2*gamma+1),
            lower_bound_minus_log_filter=gap_cost, bound_over_n_squared=gap_cost/n**2)


def gaussian_resolution():
    for s in map(mp.mpf, ("0","0.7","10","40")):
        def density(t, power, moment):
            if not t and s:
                return mp.mpf(0)
            cost = (t-s/(4*t))**2 if t else mp.mpf(0)
            return 2/mp.sqrt(mp.pi)*cost**moment*mp.exp(-power*cost)
        edges = [0,1,2,4,8,16,mp.inf]
        integral = mp.quad(lambda t: density(t,1,0), edges)
        cost = mp.quad(lambda t: density(t,1,1), edges)
        power = mp.mpf(3)/2
        tilted = mp.quad(lambda t: density(t,power,0), edges)
        assert abs(integral-1) < mp.mpf(10)**(-mp.dps+6)
        assert abs(cost-mp.mpf(1)/2) < mp.mpf(10)**(-mp.dps+6)
        assert abs(tilted-1/mp.sqrt(power)) < mp.mpf(10)**(-mp.dps+6)
        row("area_resolution", s=s, integral=integral, difference=abs(integral-1),
            heat_weighted_cost=cost, tilted_power=power, tilted_integral=tilted)


if __name__ == "__main__":
    for precision in (80,120):
        with mp.workdps(precision):
            replica()
            ads()
            horizon()
            sparse()
            gaussian_resolution()
