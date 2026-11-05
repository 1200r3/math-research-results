# Defect hierarchy and the sharp unicyclic classification

Claim C-e83ae1e1d8f8447c846f8208, revision 5. Candidate proofs of T4-T5, unchanged from revision 2. Definitions and T1-T3 are in FULL_PROOF.md and ../statement.md. Same author/context; no independent review claimed.

## 1. Balanced-gauge block identity

Fix h, and let z(t)=t h+grad phi(t) be the unique minimizing nonlinear gauge. The implicit-function argument in FULL_PROOF.md, Section 5, proves real analyticity near zero. Its oddness follows from uniqueness: phi(-t)=-phi(t) and z(-t)=-z(t). Hence e(t)=E(th), k(t), and v(t) defined in T4 are analytic even functions, all zero at t=0.

Put M(t)=A(z(t)). The nonlinear divergence condition gives both

    M(t)u=(lambda0+e(t))u+v(t),
    M(t)^T u=(lambda0+e(t))u+v(t),
    u^T v(t)=0.                                        (1.1)

The second equality uses cancellation of the negative sinh terms as well as the positive ones; it is not an assertion that M(t) is symmetric. Let P=I-u u^T and let C(t) be P M(t) P restricted to u-perp. In the orthogonal decomposition span(u) plus u-perp, the exact block form is

    M(t) = [[lambda0+e(t), v(t)^T],
            [v(t),        C(t)  ]].                    (1.2)

At t=0, C(0) is B restricted to u-perp and lambda0 is outside its spectrum. By continuity, for all sufficiently small real t, lambda(t)I-C(t) is invertible, where lambda(t)=rho(A(th)). The positive right eigenvector of M(t) has a nonzero u-component, so normalize this component to 1 and write it as u+w(t), w in u-perp. Eliminating w from the lower block equation and using the upper block equation gives

    Delta(t)=v(t)^T [lambda(t)I-C(t)]^(-1) v(t),         (1.3)
    Delta(t)=lambda(t)-lambda0-e(t).

This is a local resolvent identity. Invertibility for all large t is not asserted. At t=0 the inverse is R on u-perp.

## 2. Proof of the order hierarchy (T4)

If v is identically zero near zero, (1.1) and positivity of u give Delta=0 there. Otherwise an analytic, even, finite-dimensional vector function v with v(0)=0 has a least nonzero coefficient v_(2m), m>=1. Substituting

    v(t)=t^(2m) v_(2m)+O(t^(2m+2))

into (1.3) gives leading coefficient v_(2m)^T R v_(2m), which is strictly positive because v_(2m) is nonzero and perpendicular to u. At first the error estimate is O(t^(4m+1)); since Delta is analytic and even, its odd Taylor coefficients vanish, improving this to O(t^(4m+2)). This proves T4. For m=1, expanding k_i(t) gives v_2=K2u-a u=g, recovering the independently derived formula of T2.

In particular g=0 forces v=O(t^4) and Delta=O(t^8). It does not force Delta identically zero, as the example in Section 5 shows.

## 3. Three coefficient tests on a pure cycle

Let the cycle have length ell>=3, with cyclic edge indices i. Write r_i=1/c_i>0. At vertex i the incident cycle resistances are r_(i-1),r_i. For nonzero circulation, the scalar current J(t) from T3 is odd analytic, with

    J'(0)=Phi / sum_i r_i != 0.

Thus changing parameter from t to J is an analytic odd local change of coordinate. It preserves which is the first nonconstant even coefficient of the vector k.

The exact local row increment is

    k_i(J) = [sqrt(c_(i-1)^2+J^2)-c_(i-1)
              +sqrt(c_i^2+J^2)-c_i] / u_i^2.

Its first three even coefficients are proportional to

    (r_(i-1)+r_i)/u_i^2,
    (r_(i-1)^3+r_i^3)/u_i^2,
    (r_(i-1)^5+r_i^5)/u_i^2,                           (3.1)

with respective nonzero scalar factors 1/2, -1/8, 1/16. Since the t-to-J change is triangular with nonzero leading coefficient, the coefficients at t^2,t^4,t^6 are all constant across vertices if and only if all three quantities in (3.1) are constant across vertices.

Suppose these three tests are constant. The first yields u_i^2=K(r_(i-1)+r_i) for one K>0. On dividing the next two tests by the first, every adjacent pair (x,y) of resistances has the same values of

    Q(x,y)=(x^3+y^3)/(x+y)=x^2-xy+y^2,
    H(x,y)=(x^5+y^5)/(x+y).

For p=xy and q=Q(x,y), direct expansion gives

    H(x,y)=q^2+p q-p^2.                                (3.2)

Now compare successive adjacent pairs (x,y) and (y,z), with x,y,z>0. Equality of Q gives

    (x-z)(x+z-y)=0.                                    (3.3)

If x!=z, then y=x+z. The difference of the two values of H, using (3.2), is

    [xy-yz][q-xy-yz]
       =y(x-z)(q-y^2)
       =-xyz(x-z),                                     (3.4)

where q-y^2=-xz. This is nonzero, a contradiction. Hence z=x at every consecutive triple: the edge resistances, and therefore the c_i, are two-periodic.

The sums r_(i-1)+r_i are consequently constant, so the first test makes u uniform. Since c_i=B_(i,i+1) u_i u_(i+1), the B edge weights are two-periodic too. Their incident sums are constant. The eigenvector equation B u=lambda0 u with uniform u then forces all B_ii to be equal.

Conversely, if B has constant diagonal and two-periodic positive weights on a pure cycle, it has constant row sum and a uniform Perron vector. Formula (7.1) in FULL_PROOF.md shows that every vertex has the same k_i for every real J, so T1 is an equality for every real t. Odd ell forces the two alternating values to coincide.

## 4. Proof of T5

For a unicyclic graph with an outside vertex and Phi!=0, FULL_PROOF.md proves v_2=g!=0; T4 therefore gives a strictly positive fourth-order leading coefficient.

For a pure cycle, if one of the first three coefficient tests fails, let m in {1,2,3} be the first nonconstant even coefficient of k(t). Then v_(2m)!=0 and T4 yields leading order 4m with positive coefficient, namely 4, 8, or 12. If none fails, Section 3 gives exactly the structural equality class, and equality holds for every real t. Conversely, identically zero defect implies equality at every small t, hence k_i(t) are all equal by T1, so the three coefficient tests hold and the same structural class follows. This proves the alternatives are exhaustive and mutually exclusive.

The claim concerns the order of vanishing at t=0; an isolated equality at some nonzero value of t outside a neighborhood of zero is not classified here. Nonzero circulation is essential. For zero circulation all twists are diagonally similar to B regardless of graph weights.

## 5. Sharp eighth-order example

Take the symmetric rational matrix

    B = [[3/4,  1/12,   1/12],
         [1/12, 13/14,  1/63],
         [1/12, 1/63,   13/14]].

Here lambda0=1 and the unnormalized Perron vector is U=(2,3,3)^T with mass M=22. Use unnormalized conductances C_ij=B_ij U_i U_j: along 1->2->3->1 these are (1/2,1/7,1/2), with resistances (2,7,2). Set h=(2/11,7/11,2/11) along that orientation, and use negative values on reversed edges. This is the harmonic representative with total circulation 1. Scaling U to u=U/sqrt(M) gives c=C/M and leaves the minimizing gauge unchanged. The local increments can be computed as k_i=U_i^(-2) sum_j C_ij[cosh(z_ij)-1]. If F_C denotes the raw functional 2 sum_E C_e[cosh(h_e+grad phi_e)-1], then F_c=F_C/M and the normalized energy in the statement is E=(min_phi F_C)/M. The raw minimum itself is not invariant under this scaling.

Let R0=11 be the sum of the unnormalized resistances, and let j denote the corresponding unnormalized nonlinear current. It satisfies 2 asinh(2j)+asinh(7j)=t. The first coefficient test is constant, but the second is not: the incident cubic-resistance sums divided by U_i^2 are (4,39,39). Thus the leading defect is eighth order.

For the explicit coefficient, the coefficient of t^4 in (k(t)-E(t))U is

    G4 = [105/(4*11^5)] (3,-1,-1)^T.

This follows from

    j(t)=t/R0 + (sum r_e^3)t^3/(6 R0^4)+O(t^5),
    k_i(j)=j^2(sum_incident r)/(2U_i^2)
            -j^4(sum_incident r^3)/(8U_i^2)+O(j^6),

and centering with weights U_i^2/M. The vector (3,-1,-1) is an eigenvector of B with eigenvalue 25/36 and is perpendicular to U. Therefore R G4=(36/11)G4, and T4 in unnormalized coordinates gives

    Delta(t)=[G4^T R G4/M]t^8+O(t^10)
            =[99225/(8*11^11)]t^8+O(t^10).              (5.1)

The normalized vector v_4 is G4/sqrt(M). This explicit normalization prevents a hidden factor of M.

A separate eigenvalue check is available: if lambda=1+s, determinant expansion gives

    s(s+11/36)(s+11/126)=(cosh(t)-1)/4536.

The positive root supplies the Perron increment and is checked numerically against the full matrix in code/check_defect.py.

## 6. Sharp twelfth-order example

Use the pure four-cycle 1-2-3-4-1, unnormalized Perron vector U=(3,3,4,4), mass M=50, and unnormalized conductances

    C=(3/2,3/25,3/23,3/25).

Define a symmetric B by B_ij=C_ij/(U_i U_j) on these edges, zero on the nonedges, and

    B_ii=1-sum_j C_ij/U_i^2.

Explicitly,

    B = [[41/50, 1/6,   0,       1/100],
         [1/6,   41/50, 1/100,   0],
         [0,     1/100, 566/575, 3/368],
         [1/100, 0,     3/368,   566/575]].

All entries on the graph and on the diagonal are positive; B U=U, so lambda0=1. The resistances are (2/3,25/3,23/3,25/3), their sum is R0=25, and h=(2/75,1/3,23/75,1/3) is harmonic with circulation 1.

At every vertex the first normalized odd-resistance moment is 1 and the third is 193/3. The fifth has two distinct values. Let a=2/3, b=23/3 and m=a+b=25/3. The two adjacent-pair types are (a,m) and (m,b); their fifth-to-first moment ratio differs by

    abm(b-a)=8050/27.

As the first two tests are constant, all their contributions from the series j(t) cancel upon centering k(t). The coefficient of t^6 in (k(t)-E(t))U is therefore exactly

    G6_i = U_i [F_i - sum_j U_j^2 F_j/M] / (16 R0^6),
    F_i=(r_(i-1)^5+r_i^5)/U_i^2,
    G6=[161/(18*25^6)](4,4,-3,-3)^T.

The vector (4,4,-3,-3) is perpendicular to U and satisfies (I-B)v=v/48. Its squared norm equals M=50. Thus

    Delta(t)=[G6^T R G6/M]t^12+O(t^14)
            =[103684/(27*25^12)]t^12+O(t^14).           (6.1)

Every displayed rational identity is checked by code/check_hierarchy.py. The Decimal calculation checks convergence of Delta(t)/t^12 toward this positive rational constant. The fourth-order example is FULL_PROOF.md, Section 8. Together these prove sharpness of all three alternatives by explicit mathematical witnesses, with numerical checks as supplementary evidence.

## 7. Proven scope and open questions

T4-T5 and the three examples now have complete candidate derivations. The cycle classification does not cover isolated equality away from zero or uniform remainder estimates as B varies. Revision 3 additionally resolves the existence of every order 4m on general graphs in ARBITRARY_ORDER.md; it does not classify each general graph. Novelty relative to matrix balancing, current cumulants, and variational-eigenvalue literature remains pending detailed comparison. No independent or Lean validation is implied.
