"""Finite double-sided contractions for the phase 2 operator counterexample."""

from cmath import exp as phase_exp
from itertools import combinations
from math import cos, exp, isclose, pi


def weighted_vector(labels, rapidity):
    """Amplitudes of |label> x |label*> for C_b P, boosted on the second side."""
    amplitudes = {}
    for n, side in labels:
        s = 1 if side == "L" else 3
        cap_weight = exp(-s / 2 - (s - 3) ** 2 / 4)
        amplitudes[n, side] = cap_weight * phase_exp(1j * rapidity * s / (2 * pi))
    return amplitudes


def flip_expectation(amplitudes):
    """Unnormalized expectation of minus the simultaneous flip of both sides."""
    value = 0j
    for (n, side), amplitude in amplitudes.items():
        partner = (n, "R" if side == "L" else "L")
        value -= amplitudes.get(partner, 0j).conjugate() * amplitude
    assert abs(value.imag) <= 1e-10
    return value.real


def compare(labels):
    initial = weighted_vector(labels, 0)
    boosted = weighted_vector(labels, pi)
    norm_sq = sum(abs(coefficient) ** 2 for coefficient in initial.values())
    raw_change = flip_expectation(boosted) - flip_expectation(initial)
    delta = 1 - cos(1)
    return raw_change / norm_sq, raw_change - delta * norm_sq / 2


def cycle_union(indices):
    labels = set()
    for n in indices:
        labels.add((n, "R"))
        labels.update((j, "L") for j in range(7 * n - 6, 7 * n + 1))
    return labels


def main():
    delta = 1 - cos(1)
    weight = exp(-3)
    print("N    paired change    cycle change    paired Z[X]    cycle Z[X]")
    for count in (1, 8, 64, 256):
        indices = range(1, count + 1)
        paired = {(n, side) for n in indices for side in ("L", "R")}
        paired_change, paired_raw = compare(paired)
        cycle_change, cycle_raw = compare(cycle_union(indices))
        assert isclose(paired_change, delta, rel_tol=1e-11)
        assert isclose(cycle_change, delta / 4, rel_tol=1e-11)
        assert isclose(paired_raw, count * weight * delta, rel_tol=1e-11)
        assert isclose(cycle_raw, -2 * count * weight * delta, rel_tol=1e-11)
        print(f"{count:<4} {paired_change:14.9f} {cycle_change:14.9f}"
              f" {paired_raw:14.9f} {cycle_raw:14.9f}")

    # The general estimate applies even if the selected cycles are not adjacent.
    for size in range(1, 9):
        for indices in combinations(range(1, 9), size):
            change, raw = compare(cycle_union(indices))
            assert change <= delta / 4 + 1e-12
            assert raw <= -2 * weight * delta * size + 1e-12
    print("Checked all 255 nonempty subsets of the first 8 complete cycles.")


if __name__ == "__main__":
    main()
