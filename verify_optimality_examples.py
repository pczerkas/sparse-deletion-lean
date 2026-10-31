#!/usr/bin/env python3
"""Exact arithmetic checks for the two-stage sparse-deletion example.

This is not a formal Lean proof of the infinite construction.
"""

from math import isqrt

FIRST_DELETED = (1, 2, 6, 9, 20)
SECOND_DELETED = (88, 89, 94, 180, 276)


def square_pyramid(n: int) -> int:
    return n * (n + 1) * (2 * n + 1) // 6


def triangular(n: int) -> int:
    return n * (n + 1) // 2


def is_triangular(value: int) -> tuple[bool, int]:
    t = isqrt(8 * value + 1)
    return t * t == 8 * value + 1 and (t - 1) % 2 == 0, (t - 1) // 2


def check(n: int, deleted: tuple[int, ...], expected_index: int) -> None:
    assert len(set(deleted)) == len(deleted)
    assert all(0 < k <= n for k in deleted)
    result = square_pyramid(n) - sum(k * k for k in deleted)
    is_tri, index = is_triangular(result)
    assert is_tri and index == expected_index, (n, result, index)
    print(f"n={n}: P(n)-sum(deletions^2)={result}=T({index}), "
          f"deleted={len(deleted)}")


if __name__ == "__main__":
    assert min(SECOND_DELETED) > 87, "Second stage must preserve the first hit"
    check(87, FIRST_DELETED, 667)
    check(3500, FIRST_DELETED + SECOND_DELETED, 169101)
    assert sum(k * k for k in FIRST_DELETED) == 522
    assert sum(k * k for k in SECOND_DELETED) == 133077
    print("All exact checks passed.")
