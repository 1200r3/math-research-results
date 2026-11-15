"""Check C02's generated search certificate without importing its producer."""

from collections import Counter
from hashlib import sha256
from itertools import combinations
from json import loads
from pathlib import Path
from sys import argv
from time import perf_counter


def geometry(n):
    points = [(i, j) for i in range(n) for j in range(n) if i+j < n]
    index = {p: i for i, p in enumerate(points)}
    edges = set()
    for ((a, (x, y)), (b, (u, v))) in combinations(enumerate(points), 2):
        r, s = u-x, v-y
        # The only third vertices are rotations of (r,s) by plus/minus 60 degrees.
        for p in ((x-s, y+r+s), (x+r+s, y-r)):
            c = index.get(p)
            if c is not None:
                if c == a or c == b:
                    raise ValueError("a rotation of a nonzero vector gave a repeated point")
                edges.add(tuple(sorted((a, b, c))))
    return points, sorted(edges)


def close(vertices, edges):
    """Apply same-color pair exclusions by repeatedly scanning every edge."""
    while True:
        changed = False
        for x, y, z in edges:
            for a, b, c in ((x, y, z), (y, z, x), (z, x, y)):
                if len(vertices[a]) == 1 and vertices[a] == vertices[b]:
                    remainder = vertices[c] - vertices[a]
                    if not remainder:
                        return False
                    if remainder != vertices[c]:
                        vertices[c] = remainder
                        changed = True
        if not changed:
            return True


def check(tree, vertices, edges, counts):
    if not close(vertices, edges):
        if tree is not None:
            raise ValueError("branch has a valid contradiction but is not a leaf")
        counts["verified_contradiction_leaves"] += 1
        return
    if not isinstance(tree, list) or len(tree) != 2:
        raise ValueError("leaf lacks an independently verified contradiction")
    v, cases = tree
    if type(v) is not int or not 0 <= v < len(vertices) or len(vertices[v]) < 2 or not isinstance(cases, list):
        raise ValueError("invalid branch variable or cases")
    if any(not isinstance(case, list) or len(case) != 2 or type(case[0]) is not int for case in cases):
        raise ValueError("invalid branch case")
    if sorted(c for c, _ in cases) != sorted(vertices[v]):
        raise ValueError("branches do not cover the available colors exactly")
    counts["verified_split_nodes"] += 1
    for color, child in cases:
        new_vertices = vertices.copy()
        new_vertices[v] = frozenset({color})
        check(child, new_vertices, edges, counts)


def main():
    path = Path(argv[1])
    results = loads(Path(argv[2]).read_bytes())
    raw = path.read_bytes()
    proof = loads(raw)
    if (proof["n"], proof["k"]) != (9, 3):
        raise ValueError("certificate target must be T9 and 3 colors")
    if sha256(raw).hexdigest() != results["certificate_sha256"]:
        raise ValueError("certificate does not match the search record")
    for n in range(2, 14):
        points, edges = geometry(n)
        horizontal = sum(
            len({points[v][1] for v in e}) < 3
            for e in edges
        )
        expected = results["geometry"][f"T{n}"]
        if (len(points), len(edges), horizontal) != (expected["points"], expected["triangles"], expected["horizontal_edge"]):
            raise ValueError(f"independent rotation geometry mismatch T{n}")
        print(f"T{n} via ±60 degrees: {len(points)} points, {len(edges)} triangles ({horizontal} horizontal)", flush=True)
    points, edges = geometry(9)
    counts = Counter()
    start = perf_counter()
    check(proof["tree"], [frozenset({0, 1, 2})] * len(points), edges, counts)
    print(f"T9/3 certificate verified: {dict(counts)}, {perf_counter() - start:.6f} seconds", flush=True)
    print("PASS", flush=True)


if __name__ == "__main__":
    main()

