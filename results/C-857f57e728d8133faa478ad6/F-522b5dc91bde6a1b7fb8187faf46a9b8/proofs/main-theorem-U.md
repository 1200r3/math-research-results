# Proof of the three-color classification

Use color labels 0,1,2, with the color-i equation x+y+c_i=z. The coloring is a map, so its range need not contain every label. The exact diagonal value is due to D. Schaal, *A Family of 3-Color Rado Numbers*, Congr. Numer. 111 (1995), 150–160; the scaling proof below follows Adhikari et al., Math. Comp. 85 (2016), Proposition 4.9 and Corollary 4.10, doi:10.1090/mcom3034.

## Off the diagonal

For a nonconstant triple take s=min v₂(c_i−c_j) over nonzero pairwise differences, and put m=2^s. The shifts agree modulo m, but not modulo 2m. Thus exactly two shifts have the same residue a modulo 2m and the third has residue a+m modulo 2m. Relabel colors so the first two agree. For the translated variables u=x+a−1, v=y+a−1, w=z+a−1 the residue equation is u+v+(c_i−a+1)=w modulo 2m. Hence it suffices to avoid the shifts (1,1,1+m) modulo 2m. Any lift to the integers followed by restriction to positive integers is valid.

For the unique representative hm+r with h=0 or 1 and 0≤r<m, use color r modulo 3 when h=0 and color 1+q−r modulo 3 when h=1, where q=m modulo 3 is represented by +1 or −1. Suppose a monochromatic solution of color i exists, and write H=h_u+h_v−h_w and δ=1 for i=2 and 0 otherwise. Then H∈{−1,0,1,2}. The congruence implies
`r_u+r_v+1−r_w = jm`
with j≡H+δ (mod 2). The expression is between 2−m and 2m−1, so j∈{0,1}; this also holds for m=1. A representative of color i has
`r ≡ i + (1+q−2i)h (mod 3).`
Thus a solution would require
`i+1+(1+q−2i)H−jq ≡ 0 (mod 3).`
Using j=(H+δ) mod 2 gives the following least nonnegative residues, all nonzero:

| q | i | H=−1 | H=0 | H=1 | H=2 |
|---|---|---|---|---|---|
| 1 | 0 | 1 | 1 | 2 | 2 |
| 1 | 1 | 1 | 2 | 1 | 2 |
| 1 | 2 | 2 | 2 | 1 | 1 |
| −1 | 0 | 2 | 1 | 2 | 1 |
| −1 | 1 | 2 | 2 | 1 | 1 |
| −1 | 2 | 1 | 1 | 2 | 2 |

This contradiction excludes a modular solution. Pull the coloring back along x↦(x+a−1) mod 2m, then undo the color relabeling. An integer equality would give the excluded modular solution, which proves infinity on every finite interval as well.

## On the diagonal

Write b=c+1 and replace each variable x by x+c, turning the common equation into ordinary addition on [b,N+c]. For N=13c+14 this interval contains b,2b,…,14b. Pull back their coloring to [1,14] and use the classical three-color Schur result: every coloring of [1,14] has a monochromatic u+v=w, including repeats. This proves the upper bound.

For N=13c+13, the translated interval is [b,14b−1]. Assign a color to y by which of the sets {1,4,10,13}, {2,3,11,12}, {5,6,7,8,9} contains floor(y/b). In each set A, neither u+v nor u+v+1 belongs to A for any u,v in A. Since floor((y+z)/b) differs from floor(y/b)+floor(z/b) by 0 or 1, the coloring avoids a monochromatic sum. Hence the lower bound is exact.

The argument is a paper proof. The accompanying script verifies the finite residue arithmetic, the carry-free partition, and the small classical Schur instance; it is not a Lean verification.