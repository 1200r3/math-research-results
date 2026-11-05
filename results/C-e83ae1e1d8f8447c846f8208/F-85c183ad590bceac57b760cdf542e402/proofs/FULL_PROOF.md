# Candidate proof: nonlinear cycle bound and fourth-order Perron defect

Claim C-e83ae1e1d8f8447c846f8208, revision 5. This file proves unchanged T1-T3; HIERARCHY.md proves T4-T5 and sharp examples; ARBITRARY_ORDER.md proves T6 and its bipartite lift; DIMENSION.md proves T7-T8; ZERO_DIAGONAL.md proves T9. These five files together are the full candidate proof. Author derivation, not independent review. Normalization is always u^T u=1 unless explicitly stated. All edge sums count each undirected edge once; sums over neighbors are directed. The exact statement is in ../statement.md.

## 1. Preliminary linear algebra and gauge invariance

By the finite-dimensional Perron-Frobenius theorem, connected off-diagonal support makes B and every A(h) irreducible nonnegative matrices. Their Perron roots are algebraically simple and have strictly positive right eigenvectors. Primitivity is not needed. Since B is symmetric, its largest eigenvalue lambda0 is simple, and lambda0 I-B is positive definite on u-perp even when B is bipartite. Let R be its inverse on that subspace and zero on span(u).

For D=diag(exp(phi_i)), direct multiplication gives

    A(h+grad phi) = D^(-1) A(h) D.

Thus the Perron root depends only on edge data modulo gradients. Also A(-h)=A(h)^T, so rho(A(-h))=rho(A(h)). These statements do not assume that the minimizing gauge is the Perron gauge.

## 2. Existence and uniqueness of the nonlinear gauge

Define F_h(phi)=2 sum_E c_ij[cosh(h_ij+phi_j-phi_i)-1] on phi_1=0. It is smooth and strictly convex: its Hessian quadratic form is

    2 sum_E c_ij cosh(h_ij+phi_j-phi_i)(v_j-v_i)^2,

strictly positive for every nonzero v with v_1=0 because G is connected. For any K >= 0, if F_h(phi) <= K then each nonnegative edge term is at most K. Thus |h_e + grad(phi)_e| <= arcosh(1+K/(2c_e)) on every edge, so |grad(phi)_e| <= |h_e|+arcosh(1+K/(2c_e)). Summing these bounds along a fixed path from the pinned vertex 1 to each vertex bounds every coordinate of phi on the entire sublevel set. Sublevel sets are closed by continuity and hence compact. The nonempty sublevel F_h(phi) <= F_h(0) contains a minimizer; strict convexity makes it unique.

Differentiation with respect to phi_i gives -2 sum_j c_ij sinh(z_ij), where z=h+grad phi. The pinned stationarity equations imply the remaining equation too, since the sum of the divergences is zero. Thus the minimizer is characterized by

    sum_j c_ij sinh(z_ij)=0 for all i.                     (2.1)

## 3. Perron lower bound and all equality cases

Let r>0 be a right Perron vector of A(h). Write r_i=u_i exp(q_i) and fix the irrelevant additive constant in q by q_1=0. Divide the i-th eigenvector equation by r_i, multiply by u_i^2, and sum over i. Pairing the two orientations of every edge gives

    rho(A(h)) = sum_i B_ii u_i^2
                + 2 sum_E c_ij cosh(h_ij+q_j-q_i).

On the other hand u^T B u=lambda0=sum_i B_ii u_i^2+2 sum_E c_ij. Therefore the following exact identity holds at the Perron gauge q:

    rho(A(h))-lambda0=F_h(q) >= min_phi F_h(phi)=E(h).    (3.1)

This is an elementary proof of the specialized variational lower bound. The general variational antecedent is known; the present proof is included for completeness.

For the minimizing z, (2.1) cancels the sinh terms and yields

    [A(z)u]_i/u_i = B_ii + u_i^(-2) sum_j c_ij exp(z_ij)
                  = lambda0 + k_i,
    k_i = u_i^(-2) sum_j c_ij[cosh(z_ij)-1].             (3.2)

If all k_i are equal to k, then u is a positive eigenvector of A(z), hence its eigenvalue lambda0+k is the Perron root. The weighted average sum_i u_i^2 k_i equals E(h), proving equality in (3.1). Conversely, equality in (3.1) implies that the Perron gauge q is the unique minimizing gauge. Its eigenvector equation and (3.2) force all k_i to equal rho(A(h))-lambda0. This proves T1 in both directions. In particular E(h)=0 exactly for gradient edge data (zero circulation around every cycle).

## 4. The harmonic representative

The strictly convex quadratic functional sum_E c_ij(h_ij+psi_j-psi_i)^2 on psi_1=0 has a unique minimizer. Its Euler equation is

    sum_j c_ij alpha_ij=0,
    alpha=h+grad psi.                                   (4.1)

For any vertex potential v, summation by parts gives

    sum_E c_ij alpha_ij(v_j-v_i)
      = -sum_i v_i sum_j c_ij alpha_ij = 0.              (4.2)

In particular alpha, a, b, g, and R in T2 are independent of which representative h is used. Only R depends solely on B.

## 5. Expansion of the minimum energy

Gauge invariance lets us replace h by alpha. Let eta(t), pinned at vertex 1, minimize F_{t alpha}; eta(0)=0. Its stationarity equations are analytic in (t,eta). Their derivative in eta at (0,0) is minus the grounded positive weighted Laplacian, hence invertible. The analytic implicit-function theorem gives an analytic eta(t) near zero; strict convexity identifies this solution with the global minimizer.

Equation (4.1) implies eta'(0)=0. Uniqueness and the oddness of sinh give eta(-t)=-eta(t). Consequently eta(t)=t^3 eta3+O(t^5). Let beta=grad eta3. Taylor expansion gives

    2[cosh(t alpha_e+t^3 beta_e+O(t^5))-1]
      = t^2 alpha_e^2
        + t^4[2 alpha_e beta_e+alpha_e^4/12]+O(t^6).

After multiplication by c_e and summation, the cross term vanishes by (4.2). There are finitely many edges. Thus

    E(th)=a t^2+b t^4+O(t^6),
    a=sum_E c_e alpha_e^2,
    b=(1/12)sum_E c_e alpha_e^4.                         (5.1)

The O(t^6) statement is local for each fixed B and h; no uniform remainder over varying graphs is claimed.

## 6. Expansion of the Perron eigenvalue

Write

    A(t alpha)=B+tK1+t^2K2+t^3K3+t^4K4+...,

where Kr_ij=B_ij alpha_ij^r/r! for i!=j and Kr_ii=0 for r>=1. Odd Kr are skew-symmetric, even Kr are symmetric. Equation (4.1) implies K1 u=0 and u^T K1=0.

The algebraic simplicity of lambda0 and the analytic implicit-function theorem give analytic eigenvalue lambda(t) and eigenvector r(t), normalized by u^T r(t)=1. For small real t the eigenvector is positive by continuity and so lambda(t)=rho(A(t alpha)). Transposition gives lambda(t)=lambda(-t); therefore it has only even powers. Write

    lambda(t)=lambda0+a2 t^2+a4 t^4+O(t^6),
    r(t)=u+t r1+t^2 r2+t^3 r3+...,
    u^T rj=0 for j>=1.

Comparing first-order terms gives (lambda0 I-B)r1=K1 u=0, so r1=0. At order two,

    (lambda0 I-B)r2=(K2-a2 I)u,
    a2=u^T K2u=sum_E c_e alpha_e^2=a,
    r2=R g,  g=K2u-a u.                                (6.1)

This also proves g is perpendicular to u. At order four, multiply the coefficient equation by u^T. Normalization and r1=0 eliminate all eigenvector normalization terms, while u^T K1=0 eliminates the r3 term. We obtain

    a4=u^T K4u+u^T K2r2
       =(1/12)sum_E c_e alpha_e^4+g^T Rg
       =b+g^T Rg.                                      (6.2)

Combining (5.1) and (6.2) proves T2. R is positive definite on u-perp, so g^T Rg>=0 with equality exactly for g=0. If lambda2 denotes the second-largest eigenvalue of B and lambdamin the smallest, spectral decomposition also gives the useful bounds

    ||g||^2/(lambda0-lambdamin) <= g^T Rg
                               <= ||g||^2/(lambda0-lambda2).

No claim that zero quartic coefficient forces equality for all t is made here.

## 7. The unicyclic reduction

Define the antisymmetric current j_ij=c_ij sinh(z_ij) for the minimizing gauge. It is divergence-free by (2.1). On a bridge, summing divergence over one component of its removal shows that the current is zero, so z is zero on every bridge. On the unique oriented cycle, conservation implies a common current J. Thus

    z_e=asinh(J/c_e) on the oriented cycle.

Gradients have zero cycle circulation. Hence sum_C asinh(J/c_e)=Phi. Its left side is continuous, strictly increasing and ranges from minus infinity to plus infinity. This proves the unique J exists for every real Phi. Conversely these z values have the same single circulation as h and differ from h by a gradient: integrate along any spanning tree, and the remaining edge follows from equality of circulation. They satisfy (2.1), so they are the minimizer.

Using cosh(asinh(x))=sqrt(1+x^2) gives

    E(h)=2 sum_C[sqrt(c_e^2+J^2)-c_e].                   (7.1)

If Phi!=0, then J!=0. Every cycle vertex has k_i>0, while every vertex outside the cycle has k_i=0 because all its incident edges are bridges. Thus equality in T1 is impossible if any vertex lies outside the cycle. If Phi=0, then J=0 and all z vanish, so A(h) is diagonally similar to B. This proves T3.

For completeness, the harmonic representative on the same graph is alpha_e=Phi/(c_e S) on the oriented cycle and zero off it, where S=sum_C c_e^(-1). Thus a=Phi^2/S. If Phi!=0 and an outside vertex exists, g_i=-a u_i!=0 there; the quartic defect is strictly positive too.

## 8. Explicit exact example, with an independent algebraic route

Take

    B = [[2,1,1,0],
         [1,2,1,0],
         [1,1,1,1],
         [0,0,1,3]].

Its row sums equal 4, so lambda0=4 and u=(1,1,1,1)^T/2. It is 4I minus the graph Laplacian of a triangle 1-2-3-1 with leaf 4 attached to vertex 3. Its eigenvalues are 4,3,1,0. Put h_12=h_23=h_31=1/3, h_34=0, with reversed orientations negative. The total circulation of t h is t, and alpha=h.

All cycle c_e=1/4. Directly,

    a=1/12, b=1/1296,
    g=(1,1,1,-3)^T/72,
    Rg=(5,5,1,-11)^T/288,
    g^T Rg=11/5184.

The vector displayed for Rg has zero sum and its product by 4I-B is g; this is an exact rational certificate. Therefore

    E(t h)=(3/2)[cosh(t/3)-1],
    rho(A(t h))=4+t^2/12+5t^4/1728+O(t^6),
    rho(A(t h))-4-E(t h)=11t^4/5184+O(t^6).             (8.1)

An algebraically distinct verification uses the characteristic polynomial. In the permutation expansion of det(lambda I-A(t h)), a fixed point contributes its unchanged diagonal entry and a transposition along an edge contributes an unchanged product because opposite twists cancel. No permutation cycle of length greater than two can use the leaf. The only varying terms are the two oriented 3-cycles on vertices 1,2,3, with vertex 4 fixed. Each 3-cycle has positive permutation sign, three negative off-diagonal factors, and contributes -(lambda-3)exp(+t) or -(lambda-3)exp(-t). Subtracting the t=0 terms gives exactly the second term below; no further factor of lambda-4 occurs. Since the untwisted eigenvalues are 4,3,1,0,

    det(lambda I-A(t h))
      =lambda(lambda-1)(lambda-3)(lambda-4)
       -2(cosh(t)-1)(lambda-3).

Writing lambda=4+s, this is

    (1+s)[s(s+3)(s+4)-2(cosh(t)-1)].

The function s(s+3)(s+4) is strictly increasing from zero to infinity on s>=0. The Perron root is >=4 by T1 and hence corresponds to the unique nonnegative solution. The determinant alone and positivity at t=0 also identify the local analytic branch. Comparing coefficients in

    12s+7s^2+s^3=2(cosh(t)-1)

gives s=t^2/12+5t^4/1728+O(t^6), independently checking all constants in (8.1). This is a second calculation by the same author, not an independent reviewer.

## 9. Scope and limits

T1-T3 are proved above as candidate mathematics, pending external review. The broad variational principle and the nonlinear divergence-free gauge have close prior literature; they are explicitly not claimed as novel. The exact fourth-order defect formula and related extensions require further novelty comparison. Computation can check examples and detect mistakes, but is not used to prove the universal statements. Lean has not verified this claim. No external review, fixed status, publication, or upload is asserted.
