#!/usr/bin/env python3
"""Exact modular enumeration for the cubic triangular-square sieve.

All arithmetic is modulo a prime p. A residue y is triangular mod p iff
8*y+1 is a quadratic residue. This script checks candidate frequencies
for every additive shift b and each prime 37 <= p <= max_p.

This is FINITE experimental evidence, not a proof of a bound for all primes.
No non-standard Python packages are required.
"""

from argparse import ArgumentParser
from math import isqrt


def prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % k for k in range(2, isqrt(n) + 1))


def max_candidate_count(p: int) -> tuple[int, int]:
    assert p >= 37 and prime(p)
    inv6 = pow(6, -1, p)
    square = {x * x % p for x in range(p)}
    residues = [(8 * x * (x + 1) * (2 * x + 1) * inv6 + 1) % p
                for x in range(p)]
    best = (-1, -1)
    for b in range(p):
        count = sum((z + 8 * b) % p in square for z in residues)
        if count > best[0]:
            best = (count, b)
    return best


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--max-prime", type=int, default=500)
    args = ap.parse_args()
    results = []
    for p in range(37, args.max_prime + 1):
        if not prime(p):
            continue
        c, shift = max_candidate_count(p)
        results.append((p, c, shift))
    worst = max(results, key=lambda row: row[1] / row[0])
    print(f"Primes checked: {len(results)}")
    print(f"Worst ratio: {worst[1]}/{worst[0]} at p={worst[0]}, shift={worst[2]}")
    print("p   max_candidates  ratio  argmax_shift")
    for p, c, shift in results[:20]:
        print(f"{p:3d} {c:3d} {c / p:9.6f} {shift:3d}")
    print(f"All inspected primes satisfy max ≤ 3p/4: "
          f"{all(4 * c <= 3 * p for p, c, _ in results)}")


if __name__ == "__main__":
    main()
