"""Exact arithmetic regression for Gajdzica (2024), Example 4.6.

For n=r+300*k, 0<=r<300 and each shift j=0,...,4, put
q=k+(r+j)//300 and s=(r+j)%300. The partition count is the sum
of binom(s+300*i+3,3) for 0<=i<=q. Summing a cubic yields a
polynomial of degree at most four in k. Thus h_A on each class is a
polynomial of degree at most eight. Nine exact values determine it.
"""
from collections import Counter
from fractions import Fraction
from math import comb, factorial
import json

M = 300


def partition(n):
    return sum(comb(n - M * i + 3, 3) for i in range(n // M + 1))


def half_transform(n):
    a, b, c, d, e = (partition(n + i) for i in range(5))
    return 3 * c * c - 4 * b * d + a * e


def difference_heads(values):
    while values:
        yield values[0]
        values = [b - a for a, b in zip(values, values[1:])]


def main():
    results = []
    ordinary = Fraction(1, 1080000)
    exceptional = 151 * ordinary
    printed = Fraction(1, 2**3 * 3**3 * 5**4)
    for r in range(M):
        diffs = list(difference_heads([half_transform(r + M * k) for k in range(9)]))
        if any(diffs[5:]) or not diffs[4] > 0:
            raise ArithmeticError(f"Expected degree four and a positive coefficient, residue {r}")
        coefficient = Fraction(diffs[4], factorial(4) * M**4)
        expected = exceptional if (r + 4) % M == 0 else ordinary
        if coefficient != expected:
            raise ArithmeticError(f"Wrong coefficient on residue {r}: {coefficient}")
        results.append(str(coefficient))
    print(json.dumps({
        "source": "https://doi.org/10.1007/s40993-024-00532-7, Example 4.6",
        "partition_family": {"d": 2, "m": M},
        "expression": "h_A(n) = T_2(p_A)(n)/2",
        "variable": "n",
        "degree_by_residue": 4,
        "residues_checked": M,
        "exact_values_per_residue": 9,
        "special_residue": 296,
        "ordinary_leading_coefficient": str(ordinary),
        "exceptional_leading_coefficient": str(exceptional),
        "printed_lower_bound_coefficient": str(printed),
        "printed_over_ordinary": str(printed / ordinary),
        "coefficient_multiplicities": dict(Counter(results)),
        "coefficients_indexed_by_residue": results,
    }, indent=2))


if __name__ == "__main__":
    main()
