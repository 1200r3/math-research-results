# Arbitrarily high defect orders on multicyclic graphs

Claim C-e83ae1e1d8f8447c846f8208, revision 5, unchanged T6 from revision 3. This is a same-author candidate derivation, not independent review. DIMENSION.md gives the later smaller realization without replacing this preserved construction.

For every integer m>=1 there is a connected symmetric nonnegative matrix B of size 4m+2, with positive diagonal, and real antisymmetric edge data h such that

    rho(A(t h))-rho(B)-E(t h)
      = t^(4m)/(2((2m)!)^2) + O(t^(4m+2)).             (1)

Thus every nonzero order permitted by T4 actually occurs; the upper order 12 in T5 is special to unicyclic support.

## 1. An exact moment identity

For a=1,...,m let x_a=a^2 and

    d_a = 1 / [x_a product_{b!=a}(x_a-x_b)].

Empty products equal 1. Lagrange interpolation of x^(j-1) at the m distinct points x_a, followed by comparing the coefficient of x^(m-1), gives

    sum_a d_a a^(2j)=0 for 1<=j<m,
    sum_a d_a a^(2m)=1.                                (2)

This argument also covers m=1, where d_1=1. It does not need an unproved moment-matching existence assertion.

Put w_a^+=1+max(d_a,0) and w_a^-=1+max(-d_a,0). Both are positive rationals, and w_a^+-w_a^-=d_a. Define

    lambda0=2+2 sum_a max(w_a^+,w_a^-).

## 2. A simple graph realizing the moment data

Let L=2m+1. Use two vertex sets labelled (+,i) and (-,i), i in Z/LZ. Within each set, join i to i+a for every a=1,...,m. These are exactly the edges of a complete simple graph K_L, each occurring once: an unordered difference modulo odd L has one representative among 1,...,m. Give edges in color a weight w_a^+ in the plus set and w_a^- in the minus set. Give the matching edge (+,i)--(-,i) weight 1.

On the orientation i->i+a set h=a, and set h=-a on the reverse orientation. On the matching set h=0. Every vertex has one incoming and one outgoing edge of each color with identical weights. Diagonal entries of B in group sign sigma are

    B_ii=lambda0-1-2 sum_a w_a^sigma >= 1.

All row sums of B equal lambda0, so its normalized Perron vector is uniform, u_i=1/sqrt(2L). The support graph is connected and simple; all off-diagonal weights on its support are positive.

For each t, every color contributes w_a^sigma sinh(t a) and its negative to the nonlinear divergence at a vertex. Matching edges contribute zero. Therefore the zero potential is exactly the minimizing nonlinear gauge, by T1's uniqueness.

The local row increments are constant within each group:

    k_sigma(t)=2 sum_a w_a^sigma [cosh(a t)-1].

The two groups have equal total Perron mass, hence

    E(t h)=[k_+(t)+k_-(t)]/2.                           (3)

## 3. Exact quotient eigenvalue and the defect

The subspace of vectors constant on each group is invariant under A(t h). On that subspace the matrix is

    [[lambda0-1+k_+(t), 1],
     [1, lambda0-1+k_-(t)]].

Its largest eigenvalue has a positive two-component eigenvector. Lifting this vector to the full graph produces a strictly positive eigenvector. Perron-Frobenius therefore identifies the full matrix's Perron root, not just a quotient eigenvalue:

    rho(A(t h))=lambda0-1+[k_+(t)+k_-(t)]/2
                +sqrt(1+[(k_+(t)-k_-(t))/2]^2).

Let

    D(t)=sum_a d_a[cosh(a t)-1].

Equations (2)-(3) give the exact, global formula

    Delta(t)=sqrt(1+D(t)^2)-1,
    D(t)=t^(2m)/(2m)!+O(t^(2m+2)).                     (4)

Expanding sqrt(1+s^2)-1=s^2/2+O(s^4) proves (1). For m=1 the O(t^8) from the square-root expansion is smaller than the stated O(t^6), so the same remainder statement remains valid. The coefficient is strictly positive, showing the defect is not identically zero.

## 4. A zero-diagonal bipartite realization

The same defect function can be realized by a connected zero-diagonal bipartite matrix of size 8m+4. Given the matrix B above, define

    Bhat=[[0,B],[B,0]],  Ahat(t)=[[0,A(th)],[A(th),0]].

The support is simple and bipartite. It is connected because the original support is connected and B has positive diagonal, which connects each pair of corresponding vertices in the two sheets. The reciprocal edge condition holds: the reverse of the cross-sheet entry B_ij exp(t h_ij) is B_ji exp(-t h_ij). Original diagonal entries become cross-sheet edges with zero twist.

If r>0 is a Perron eigenvector of A(th), then (r,r)>0 is an eigenvector of Ahat(t) with the same eigenvalue. Thus their Perron roots agree. The normalized base vector is (u,u)/sqrt(2). In the energy minimization for Bhat, swapping the sheets preserves the functional. The minimizing potential is unique modulo a constant; invariance under the involution forces it to be sheet-symmetric, since a potential changed by a constant c under a swap would change by 2c under two swaps, hence c=0. The two copies of each original off-diagonal edge then contribute half its old energy apiece, and cross-sheet edges from B's diagonal contribute zero. Therefore Ehat(th)=E(th), so the exact defect and its leading coefficient in (1) are unchanged.

## 5. Scope

The first construction uses a positive diagonal and 4m+2 vertices; the bipartite lift uses zero diagonal and 8m+4 vertices. Minimal dimension and bounded-degree realization are not asserted. All matrices and h are explicitly defined over the rationals and integers. The proof is exact for every m, while code/check_arbitrary_order.py checks finite instances and numerical consistency. Novelty remains to be investigated separately.
