#!/usr/bin/env python3
"""Check the finite arithmetic in the paper; standard library only."""
from itertools import product


def check_table():
    rows = []
    for q, color in product((1, -1), range(3)):
        row = tuple(
            (color + 1 + (1 + q - 2 * color) * h - ((h + (color == 2)) % 2) * q) % 3
            for h in range(-1, 3)
        )
        if 0 in row:
            raise ValueError((q, color, row))
        rows.append(row)
        print(f"q={q:2} i={color}: {row}")
    return rows


def check_moduli():
    for s in range(10):
        m = 2**s
        colors = [r % 3 for r in range(m)]
        colors.extend((1 + m - r) % 3 for r in range(m))
        for x, i in enumerate(colors):
            for y, j in enumerate(colors):
                if i == j and colors[(x + y + 1 + m * (i == 2)) % (2 * m)] == i:
                    raise ValueError((s, x, y, i))
    print("Canonical residue systems checked directly for periods 2 through 1024.")


def check_diagonal():
    partition = [{1, 4, 10, 13}, {2, 3, 11, 12}, {5, 6, 7, 8, 9}]
    if sorted(x for a in partition for x in a) != list(range(1, 14)):
        raise ValueError("Not a partition")
    for a in partition:
        for x, y, carry in product(a, a, (0, 1)):
            if x + y + carry in a:
                raise ValueError((a, x, y, carry))
    print("Carry-free partition checked, including x=y.")
    # Given a valid prefix, any new sum triple ends at its new largest element.
    prefixes = [()]
    for n in range(1, 15):
        prefixes = [
            p + (c,)
            for p in prefixes
            for c in range(3)
            if not any(p[x - 1] == p[n - x - 1] == c for x in range(1, n // 2 + 1))
        ]
        print(f"Schur-free colorings on [1,{n}]: {len(prefixes)}")
    if prefixes:
        raise ValueError("A Schur-free 3-coloring of [1,14] was found")


if __name__ == "__main__":
    check_table()
    check_moduli()
    check_diagonal()
