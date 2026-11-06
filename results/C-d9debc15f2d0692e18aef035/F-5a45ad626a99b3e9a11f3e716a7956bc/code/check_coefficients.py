#!/usr/bin/env python3
"""Check the coefficient arithmetic for selected odd heights and even gaps."""
def coefficients(r, w):
    if not (w >= r >= 5 and r % 2 == w % 2 == 1):
        raise ValueError("This generating function check requires w >= r >= 5, both odd")
    a = [0] * (w + 1)
    a[0] = 1
    for k in range(1, w + 1):
        a[k] = sum(a[k - step] for step in (r - 1, r + 1) if k >= step)
    square = [sum(a[j] * a[k - j] for j in range(k + 1)) for k in range(w + 1)]
    return 4 * (a[w - r + 2] + a[w - r]), 2 * (square[w - 1] + square[w - r])


if __name__ == "__main__":
    for d in range(2, 41, 2):
        r0 = d + 5
        before = sum(coefficients(r0 - 2, r0 - 2 + d))
        target = 4 if d == 2 else 0
        if before != (8 if d == 2 else 4):
            raise ValueError((d, r0 - 2, before))
        for jump in range(0, 21, 2):
            r = r0 + jump
            if sum(coefficients(r, r + d)) != target:
                raise ValueError((d, r))
        print(f"d={d:2}: last exception r={r0 - 2:2}, count={before}; anchor={r0:2}, tail={target}")
