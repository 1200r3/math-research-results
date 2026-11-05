# Improved realization size and exact low-order minima

Claim C-e83ae1e1d8f8447c846f8208, revision 5, unchanged candidate T7-T8 from revision 4. Same-author proof; not independent review. The definitions of Delta(t), E(th), B, h and u are unchanged. Earlier claims T1-T6 are retained.

## 1. A 2m+2 vertex rational construction

Fix m>=1. Use the rational weights from ARBITRARY_ORDER.md,

    d_a=1/[a^2 product_{b!=a}(a^2-b^2)],  1<=a<=m.

They have sign (-1)^(m-a), are nonzero, and satisfy

    sum_a d_a a^(2j)=0 (1<=j<m),
    sum_a d_a a^(2m)=1.                                (1.1)

Partition the indices into P={a:d_a>0} and N={a:d_a<0}, of sizes k_+, k_- respectively, with k_++k_-=m. Let

    L_+=2k_++1,  L_-=2k_-+1,  n=L_++L_-=2m+2,
    p=L_+/n, q=L_-/n,
    w=8 L_+ L_- / n^3, gamma=n w=8pq.

Use two disjoint cyclic vertex sets of sizes L_+ and L_-. If the signed set has k indices a_1,...,a_k, put weight |d_(a_r)| on the oriented cyclic edges i -> i+r for r=1,...,k, and put h=a_r on this orientation. Reverse orientations have negative h. This forms a complete simple graph on 2k+1 vertices; no twisted edges are needed for k=0, when the group is a singleton. Join every vertex of the plus group to every vertex of the minus group with weight w and twist zero.

The outward cross-group row sums are

    eta_+=L_- w=q gamma, eta_-=L_+ w=p gamma.

Write S_+=sum_(a in P)d_a and S_-=sum_(a in N)(-d_a). Set

    lambda0=1+max(2S_++eta_+, 2S_-+eta_-),
    B_ii=lambda0-2S_sigma-eta_sigma

at vertices in group sigma. Diagonal entries are >=1, all other assigned weights are positive rationals, the support is connected, and all row sums are lambda0. Thus the normalized Perron vector is uniform, u_i=1/sqrt(n).

Each vertex has one incoming and one outgoing edge of each internal color with the same weight; cross-group twists vanish. Consequently the nonlinear sinh divergence vanishes at potential zero for every real t, which is the exact minimizing gauge by T1. The local row increments are

    k_+(t)=2 sum_(a in P)d_a[cosh(at)-1],
    k_-(t)=2 sum_(a in N)(-d_a)[cosh(at)-1],
    e(t)=E(th)=p k_+(t)+q k_-(t).

Let d(t)=k_+(t)-k_-(t). Equation (1.1) gives

    d(t)=2t^(2m)/(2m)!+O(t^(2m+2)).                    (1.2)

There is also an exact closed form. Simplifying the product in the definition gives d_a=2(-1)^(m-a)/[(m-a)!(m+a)!]. Expanding (exp(t/2)-exp(-t/2))^(2m), pairing opposite exponents, and using its value zero at t=0 yields

    d(t)=2(2 sinh(t/2))^(2m)/(2m)!.                    (1.3)

Thus d(t)>0 for every real t!=0, and no cancellation approximation is needed to evaluate it numerically.

## 2. Exact defect equation and its leading constant

The group-constant quotient is

    [[lambda0-eta_++k_+(t), eta_+],
     [eta_-, lambda0-eta_-+k_-(t)]].

Its positive Perron eigenvector lifts to a strictly positive eigenvector of the whole matrix, so its larger eigenvalue is the full Perron root. Subtracting lambda0+e(t), the trace and determinant of the quotient become respectively

    -gamma+(q-p)d(t),  -pq d(t)^2.

Therefore Delta(t) is the nonnegative root of

    Delta(t)^2 + [gamma+(p-q)d(t)] Delta(t) -pq d(t)^2=0. (2.1)

For t near zero the denominator in the following rationalized formula is positive:

    Delta(t)=2pq d(t)^2 /
      {sqrt([gamma+(p-q)d(t)]^2+4pq d(t)^2)
        +gamma+(p-q)d(t)}.                             (2.2)

In fact the formula holds for every real t with d(t)!=0, and it extends continuously by zero at d=0. Since gamma=8pq, (1.2) gives

    Delta(t)=t^(4m)/[2((2m)!)^2]+O(t^(4m+2)).          (2.3)

This matches T6's leading coefficient while using 2m+2 rather than 4m+2 vertices. When m is even the groups are equal and the entire defect function agrees with T6's old square-root formula. For odd m only the stated leading coefficient is asserted to agree; the exact function generally differs.

The zero-diagonal bipartite lift from ARBITRARY_ORDER.md, Section 4, applies because B has positive diagonal. It preserves the exact defect and uses 4m+4 vertices.

## 3. Optimality only within a precisely specified two-cell class

Define the class here as follows: B has a uniform Perron vector; its vertices are partitioned into two nonempty cells; every cross-cell edge has h=0; the zero potential is the nonlinear minimizing gauge for every t near zero; and each k_i(t) is constant within its cell for every such t. No assertion is made that all possible realizations admit this structure.

For a fixed cell, write its common local increment as a finite positive sum of functions cosh(a t)-1, with distinct positive twist magnitudes a. Let k_sigma be the number of such magnitudes. Every vertex of that cell sees all these magnitudes: equality of the local analytic functions implies equality of their coefficients, since the finite family cosh(a t)-1 is linearly independent by a Vandermonde argument. The sinh-divergence identity at a vertex holds for every t; linear independence of sinh(a t) forces the positive and negative oriented weights to balance separately at each magnitude. Hence each magnitude needs at least two distinct incident edges. Cross-cell edges have twist zero, and the graph is simple, so each cell has at least 2k_sigma+1 vertices.

The difference k_+(t)-k_-(t), if nonzero, has at most s<=k_++k_- distinct positive magnitudes. If its first nonzero coefficient is t^(2m), then s>=m: otherwise the first s equations at powers 2,4,...,2s form an invertible Vandermonde system (the squared magnitudes are distinct and nonzero) and force all signed coefficients to vanish. By T4, first defect order 4m requires precisely this first difference order 2m. Therefore any realization in this class satisfies

    n >= 2(k_++k_-)+2 >= 2m+2.                         (3.1)

The construction in Sections 1-2 attains equality. This is a restricted-class optimality result, not a global minimum-dimension theorem.

## 4. Exact global minimum dimensions at orders 4, 8 and 12

Let N_m be the least dimension n>=2 for which some B,h under the main assumptions has Delta(t)=c t^(4m)+O(t^(4m+2)), c>0. T6 already proves N_m is defined for every m. We claim

    N_1=3, N_2=3, N_3=4.                               (4.1)

If n=2, the connected simple support is a tree, so every h is a gradient and Delta is identically zero. Thus N_m>=3 for every m.

For n=3, connected support is a tree or a triangle. A triangle with zero circulation also has identically zero defect. For a triangle with nonzero circulation, suppose the t^2 and t^4 local-increment coefficients are both constant, as would be required for a twelfth-order or higher nonzero defect. Section 3 of HIERARCHY.md then yields u_i^2 proportional to the sum of the two incident resistances and a common value of

    Q(x,y)=x^2-xy+y^2

on all three unordered pairs of positive resistances. Let x be the smallest resistance and y,z the others. The function Q(x,s) is strictly increasing for s>=x, because its derivative is 2s-x>0. Thus Q(x,y)=Q(x,z) forces y=z. Comparing Q(x,y)=Q(y,y) gives x(x-y)=0, so x=y=z. The Perron vector is then uniform and T5's full equality case applies. Hence a three-vertex graph has either zero defect or leading order 4 or 8, never 12 or higher. This proves N_3>=4.

A three-vertex fourth-order witness is

    B=[[2,1,2],[1,3,1],[2,1,2]], lambda0=5,
    U=(1,1,1), M=3,
    h_12=h_23=2/5, h_31=1/5.

It is already harmonic. In the unnormalized convention of the numerical code,

    a=2/15,
    G2=K2 U-a U=(-1,2,-1)/75,
    R G2=G2/3,
    Delta(t)=(2/16875)t^4+O(t^6).

All formulas follow by direct multiplication; the displayed contrast vector is an eigenvector of B of eigenvalue 2. This proves N_1<=3. The three-vertex eighth-order witness in HIERARCHY.md Section 5 proves N_2<=3, and its four-vertex twelfth-order witness in Section 6 proves N_3<=4. Together with the lower bounds, (4.1) follows.

## 5. Remaining limits

For m>=4 the global value N_m is not determined here; only N_m<=2m+2 and N_m>=4 follow from these results. The restricted-class equality n=2m+2 must not be presented as global optimality. This file does not determine the analogous zero-diagonal minimum; ZERO_DIAGONAL.md separately settles two low-order cases under the additional bipartite restriction. Priority remains subject to the recorded literature limitations.
