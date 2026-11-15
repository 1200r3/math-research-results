# Independent computational re-review — PASS

This re-review is bound to manifest SHA-256 db647a74c005a5188534482c4202d79131b5acbbccdad5a963fc2282a021f7d1. I recomputed the manifest hash and checked all seven supplied material hashes. The six original materials are byte-for-byte identical to the versions independently reviewed below. The only added review material, evidence/verification.json, identifies and hashes the previously supplied computation log correctly. Its result is identical to the JSON in that log. A bibliographic metadata correction is outside the mathematical scope. The same independent reviewer returns this re-review; the certifying computation and the verified witness are unchanged.

I checked the full mathematical claim in the bound statement: T9 has no proper coloring with at most three colors; T12 has a proper coloring with at most four; and restriction gives f(9) = f(10) = f(11) = f(12) = 4 and f(n) >= 4 for every n >= 9. Proper means forbidding monochromatic equilateral triangles with three distinct vertices, in every orientation and of every side length.

I checked the hashes of all materials supplied with the request. The bound statement uses the exact point set and definition used in my independent enumeration. The bound coordinate witness file is byte-for-byte the input used for my independent checks (SHA-256 77cd6ec727ca019e83169c6c06e53a415a970c5f81a3cb4feffcbb9438ef08fa). I also compared each of the 78 colors in the manuscript's twelve-row table with the corresponding coordinate value in that file; all match.

## Geometry and exhaustive computation

For two points whose coordinate difference is (u,v), their squared Euclidean distance in the stated embedding is the exact integer u² + uv + v². I generated every unordered triple of distinct points and retained it when all three squared distances were positive and equal. This checks the defining geometric condition directly and has no filter on orientation.

| Board | Points | All equilateral triples | Triples without a horizontal side |
| --- | ---: | ---: | ---: |
| T8 | 36 | 210 | 92 |
| T9 | 45 | 330 | 160 |
| T10 | 55 | 495 | 260 |
| T11 | 66 | 715 | 400 |
| T12 | 78 | 1001 | 590 |

I wrote and ran an independent finite-domain search. It starts with all three colors available at every T9 vertex and uses no symmetry assumptions. If two vertices in a triple are forced to the same color, a solution cannot assign that color to the third vertex; eliminating it therefore preserves every possible proper completion. If a domain becomes empty, the branch is impossible. Each branch tries all available colors for a nonsingleton domain, and all paths are finite because each branch fixes at least one additional point. There were 2,737 split nodes, 5,496 assignments tried, and 2,760 contradiction leaves. No coloring exists. As a boundary check, the same independent program rejected two colors on T8 and found a three-color assignment, then checked it against all 210 triples. The manuscript's separate count of T8 colorings was not needed for the target claim.

The adjoining search certificate is a tree of branching vertices, available colors, and contradictions. I verified it with a separate program that does not import the search or the candidate code. This checker reconstructs the geometric triples by rotating each pair displacement by +60 and -60 degrees, then tests the tree by repeatedly scanning every triangle for necessary color deletions. It requires exact coverage of the remaining colors at every branch and proves an empty domain independently at every leaf. It verified all 2,737 split nodes and all 2,760 contradiction leaves. The certificate's SHA-256 is 3034d5c1f05e66570b36580490aa59a02bea4d178e6c0c17bb850bbc4b2bc9dd.

To replay the lower-bound certificate using Python's standard library, run from this review directory:

    python check_certificate.py T9-3-search-certificate.json certificate-geometry.json

## Upper bound and conclusion

Each of the four supplied coordinate witnesses covers exactly the relevant point set, uses permitted integer colors, and has zero monochromatic triangles among all triples in the table above for its board. For T12 the four color classes have sizes 22, 19, 19, and 18, respectively. I also explicitly checked the restrictions of the T12 coloring to T9, T10, and T11.

Since T_m is a subset of T_n whenever m <= n, any forbidden triangle in a restriction would also be forbidden in the original coloring. Thus a proper coloring restricts to a proper coloring, and f is nondecreasing. The two independently checked bounds imply the full claimed result. No four-colorability claim for T13, source-priority claim, or novelty claim is certified by this computation.

