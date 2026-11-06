# Extracting the fixed-gap one-monomino stabilization law

Let r be the shorter side, w the longer side, and count labelled tilings with one monomino. If rw is even there are no such tilings: all other tiles have area two. In particular, for a positive odd gap d there are no parity-admissible sizes at all. For even d, only odd r need be considered.

## The literature input

Use the fixed-height generating function of A. Alhazov, K. Morita and C. Iwamoto, *A Note on Tatami Tilings*, RIMS Kôkyûroku 1691 (2010), 1–7, §§3, 5 and 7, in the range of odd r≥5 and w≥r. Put P=z^(r−1)+z^(r+1). In the authors' notation, T(r,w,1) is the coefficient of z^w in B+C, where
```
B = 4(z^(r−2)+z^r)/(1−P),
C = 2(z+z^r)/(1−P)^2.
```
Here B counts a special corner block with the remaining width filled by an ordered list of pure-domino blocks. In C, a left or right single-column block L_r has width 1 and a monomino in an outer corner; the other monomino block M_r has width r. The paper's §7 expressions agree with the block widths and with the numerical table in §6. The printed second shift in the §6 formula for B is inconsistent with §7, and the printed inequality introducing §7 is reversed relative to the sequence just displayed there. We use the §7 expressions in the longer-width range supported by the block enumeration.

## Coefficient extraction

For w=r+d, the two offsets from B are d+2 and d; those from C are r+d−1 and d. The two denominators expand as ∑ P^k and ∑ (k+1)P^k, respectively. A positive exponent contributed by exactly one P must be r−1 or r+1, and at least two P factors give exponent at least 2(r−1).

For d=2 and r≥7 odd, both B offsets 4 and 2 and the second C offset 2 are strictly between 0 and r−1. The first C offset r+1 requires exactly one P and gives coefficient 2·2=4. These four tilings use L_r and one width-(r+1) pure-domino block; the monomino lies in a corner and the two axis reflections give one tiling per corner. At r=5 the same C contribution is 4, and B contributes an extra 4 because d+2=r−1, yielding 8.

For even d≥4 and odd r≥d+5, both B offsets and the second C offset are positive and smaller than r−1. The first C offset satisfies r+1 < r+d−1 < 2(r−1), so it contributes nothing. At r=d+3, B's d+2=r−1 gives coefficient 4, while its d and the second C offset are smaller than r−1. The first C offset is 2r−4, strictly between r+1 and 2(r−1) since r≥7. Thus the count is 4 at r=d+3 and vanishes at all larger admissible sizes.

## Cutoffs and scope

The last exception is r=5 for d=2 and r=d+3 for every even d≥4. The next admissible size is the least anchor: r=7 or r=d+5. If the cutoff need not itself be admissible, it is one smaller: 6 or d+4. The fixed-gap limit is 4 for d=2 and zero for even d≥4 along admissible sizes. These admissible one-monomino values agree with the submitted zero-boundary rule on this slice. When d and m are both odd the parity-filtered sequence is empty; it cannot have a uniquely defined stabilization value. For example, the unfiltered count for (d,m)=(1,1) is identically zero.

This is a corollary and reproduction of the one-monomino literature, with the threshold conventions made explicit. It leaves general fixed-m stabilization, a general closed formula and the general least threshold unresolved. The accompanying script evaluates selected coefficients independently of the submitted tiling enumeration; it is supplementary to the argument above.