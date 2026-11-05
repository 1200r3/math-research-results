# Zero-diagonal rigidity and small bipartite realizations

Claim C-e83ae1e1d8f8447c846f8208, revision 5, candidate refinement T9. Same-author derivation, not independent review. The support is the simple off-diagonal graph; all assumptions and the defect Delta are those of statement.md.

## 1. Zero-diagonal unicyclic dichotomy

Suppose B_ii=0 and G is connected and unicyclic. For any h, either Delta(t) is identically zero or its leading nonzero term has order four. Moreover, for nonzero cycle circulation, identically zero defect is exactly the pure-cycle two-periodic-weight case of T5.

Zero circulation gives diagonal similarity and zero defect. For nonzero circulation with vertices off the cycle, the quartic coefficient is strictly positive by T3 and FULL_PROOF Section 7. It remains to treat a pure cycle with nonzero circulation.

Let c_(i-1),c_i be its conductances incident at vertex i. Its harmonic field has alpha_e=J0/c_e along the cycle, where J0=Phi/(sum_e 1/c_e)!=0. If the quartic defect coefficient vanishes, T2 gives K2u=a u, with a>0. Thus

    J0^2 (1/c_(i-1)+1/c_i)=2a u_i^2.                  (1.1)

The zero-diagonal Perron equation also gives

    lambda0 u_i^2=c_(i-1)+c_i.                         (1.2)

Canceling the strictly positive sum c_(i-1)+c_i from (1.1)-(1.2) gives

    c_(i-1)c_i=lambda0 J0^2/(2a),

independent of i. Successive equations imply c_(i+1)=c_(i-1). Their incident sums are constant, so (1.2) makes u uniform. The B edge weights are therefore two-periodic, and T5 implies equality for all real t. This proves the dichotomy.

The same dichotomy holds whenever the diagonal of B is a common nonnegative constant d. Replacing B by B-dI preserves u, conductances, minimizing energy, and the defect: the positive eigenvector shows that both untwisted and twisted Perron roots decrease by exactly d. This reduction has zero diagonal and the same off-diagonal support.

## 2. Exact weighted coordinates for zero-diagonal examples

For a connected graph with positive rational conductances C_ij, let mu_i=sum_j C_ij and U_i=sqrt(mu_i). Define B_ij=C_ij/(U_i U_j) off the diagonal and B_ii=0. Then B U=U and lambda0=1. If M=sum_i mu_i, the normalized Perron vector is u=U/sqrt(M), and the conductances in the main definition are c=C/M.

The minimizing gauge can be computed using C instead of c. If alpha is the harmonic edge field and beta=grad eta3, where the cubic coefficient of the minimizing potential solves

    L_C eta3 = (1/6) div(C alpha^3),

then the local increments have coefficients

    k2_i=sum_j C_ij alpha_ij^2/(2mu_i),
    k4_i=sum_j C_ij[alpha_ij beta_ij+alpha_ij^4/24]/mu_i. (2.1)

Their means are taken with weights mu_i/M. If k2 is constant, the leading candidate residual is G4_i=U_i(k4_i-mean(k4)). T4 gives the eighth-order coefficient G4^T R G4/M. All squared-norm and Laplacian calculations below use rational numbers despite the square roots in B.

## 3. A four-vertex quartic witness

Take a four-cycle with oriented conductances C=(1,1,1,2), masses mu=(3,2,2,3), total mass M=10, and harmonic h=(2/7,2/7,2/7,1/7) along the cycle. In the coordinates of Section 2, B is zero-diagonal and bipartite. The coefficient a is 1/35 and

    f2_i=k2_i-a = (-2,3,3,-2)_i/245,
    G2=U f2.

In the coordinates G2_i=U_i f2_i with U_i=sqrt(mu_i), (B G2)_i/U_i=sum_j C_ij f2_j/mu_i=f2_i/6 by substituting the four edge conductances. Hence R G2=6G2/5. The centered vector satisfies sum_i mu_i f2_i=0 and its unnormalized squared norm is sum_i mu_i f2_i^2=(3*4+2*9+2*9+3*4)/245^2=60/245^2. Dividing by M=10 for normalization, the leading coefficient is (6/5)(60/245^2)/10=36/300125. Thus

    Delta(t)=(36/300125)t^4+O(t^6).                    (3.1)

This is a positive quartic coefficient on four vertices.

## 4. A five-vertex eighth-order witness

Take G=K_(2,3), with vertices L,R,M1,M2,M3. Use the oriented edges

    (L,M1),(M1,R),(L,M2),(M2,R),(L,M3),(M3,R),
    C=(1,4,4,1,4,4),
    h=(2,1/2,1/2,2,-1,-1).

The masses are mu=(9,9,5,5,8), total M=36. The field h is harmonic: the currents C_e h_e along the three paths L->R are 2,2,-4 and sum to zero. Equation (2.1) gives k2_i=1/2 at every vertex, so the quartic defect vanishes.

A cubic potential coefficient, up to an irrelevant common constant, is

    eta3=(5/24,-5/24,-3/8,3/8,0),

in the vertex order above. Its Laplacian equals div(C h^3)/6 exactly. Substituting beta=grad eta3 in (2.1) gives

    k4=(3/32,3/32,-1/32,-1/32,1/4),
    mean(k4)=3/32,
    f4=k4-mean(k4)=(0,0,-1/8,-1/8,5/32).

Put G4=U f4. For both L and R, sum_j C_ij f4_j=0; for every middle vertex it is zero because f4_L=f4_R=0. Hence B G4=0, R G4=G4, and

    G4^T R G4/M = sum_i mu_i f4_i^2/M = 5/512.

Thus

    Delta(t)=(5/512)t^8+O(t^10).                       (4.1)

A separate check of the Perron eigenvalue follows from the two-by-three bipartite block form. The two-by-two product block has diagonal entries 3/5 and off-diagonal entries

    (8/45)exp(5t/2)+(2/9)exp(-2t),
    (8/45)exp(-5t/2)+(2/9)exp(2t).

Its positive Perron eigenvalue is rho(A(th))^2. Consequently the exact expression is

    rho(A(th))=sqrt(3/5+sqrt(164+160cosh(9t/2))/45).    (4.2)

This spectral formula alone does not compute the minimizing energy; code/check_zero_diagonal.py separately minimizes it and compares the defect with (4.1).

## 5. Sharp bipartite zero-diagonal minima

Let Z_m be the minimum dimension among zero-diagonal B with connected bipartite support and strictly positive leading defect of order 4m. Then

    Z_1=4, Z_2=5.                                      (5.1)

Every connected bipartite simple graph on at most three vertices is a tree. On four vertices it is either a tree or a four-cycle: a bipartition has sizes 1+3 or 2+2 and at most four edges. Trees have zero defect, and Section 1 excludes order eight or higher for a zero-diagonal four-cycle. Therefore Z_1>=4 and Z_2>=5. Sections 3 and 4 attain these lower bounds.

The positive-diagonal order-12 four-cycle in HIERARCHY.md lifts to a zero-diagonal bipartite graph on eight vertices. Thus 5<=Z_3<=8. Its exact value is not proved here. For zero-diagonal graphs without a bipartite restriction, the new five-vertex example is an upper bound at order eight, not a proof that four vertices are impossible.
