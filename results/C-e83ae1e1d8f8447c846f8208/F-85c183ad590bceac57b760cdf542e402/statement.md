# Reciprocal edge twists: nonlinear bound and defect-order classification

Revision 5. Candidate main theorem; correctness and novelty are separate questions. T1-T6 are unchanged from revision 3; T7-T8 are unchanged from revision 4. T9 adds the constant-diagonal unicyclic dichotomy and exact small bipartite zero-diagonal minima. Earlier statements and claim metadata are preserved in research/.

Let n >= 2 and let B be a real symmetric entrywise nonnegative n by n matrix whose off-diagonal support graph G is connected. Diagonal entries may be nonnegative. Write lambda0 = rho(B), and choose the positive Perron vector u with sum_i u_i^2 = 1. For each undirected edge {i,j}, put c_ij = B_ij u_i u_j > 0. Each sum over E below counts an undirected edge once. Let h_ij = -h_ji be arbitrary real edge data, and set A(h)_ij = B_ij exp(h_ij) off the diagonal and A(h)_ii = B_ii.

For a vertex potential phi define (grad phi)_ij = phi_j - phi_i. Define

    E(h) = min_{phi: phi_1 = 0} 2 sum_{E} c_ij [cosh(h_ij + phi_j - phi_i) - 1].

T1. The minimum exists and is unique with this normalization. If z = h + grad phi is its minimizer, then sum_j c_ij sinh(z_ij) = 0 for every i. Moreover

    rho(A(h)) >= lambda0 + E(h).

Writing k_i = u_i^(-2) sum_j c_ij [cosh(z_ij)-1], equality holds if and only if all k_i are equal. The bound is a specialization of known variational principles, not claimed as a new principle.

T2. Let alpha = h + grad psi be the unique representative satisfying sum_j c_ij alpha_ij = 0, with psi_1 = 0. Let K2 have entries B_ij alpha_ij^2 / 2 off the diagonal and zero diagonal. Set

    a = sum_E c_ij alpha_ij^2,
    b = (1/12) sum_E c_ij alpha_ij^4,
    g = K2 u - a u.

Let R be zero on span(u) and the inverse of lambda0 I-B on u-perp. As real t tends to zero,

    E(th) = a t^2 + b t^4 + O(t^6),
    rho(A(th)) = lambda0 + a t^2 + (b + g^T R g) t^4 + O(t^6).

In particular the defect is (g^T R g)t^4 + O(t^6), its fourth-order coefficient is nonnegative, and it vanishes exactly when K2 u = a u. All quantities depend only on the gradient equivalence class of h.

T3. Suppose G is unicyclic with simple cycle C, oriented consistently, and Phi = sum_C h_ij. There is a unique real J solving

    sum_{e in C} asinh(J/c_e) = Phi.

Then

    E(h) = 2 sum_{e in C} [sqrt(c_e^2+J^2)-c_e].

If G has any vertex outside C and Phi != 0, the inequality in T1 is strict. If Phi=0, A(h) is diagonally similar to B and the defect is zero.

T4. Fix B and h. Let z(t)=t h+grad phi(t) be the minimizing gauge from T1, and write e(t)=E(t h), k_i(t)=u_i^(-2) sum_j c_ij[cosh(z_ij(t))-1], and v_i(t)=u_i[k_i(t)-e(t)]. These functions are real analytic near zero; e, k, and v are even. Either v vanishes identically near zero, in which case the defect Delta(t)=rho(A(t h))-lambda0-E(t h) also vanishes there, or there is a least positive integer m such that v(t)=t^(2m) v_(2m)+O(t^(2m+2)), with v_(2m)!=0. In the latter case

    Delta(t) = [v_(2m)^T R v_(2m)] t^(4m) + O(t^(4m+2)),

with strictly positive coefficient. In particular, a zero fourth-order coefficient implies Delta(t)=O(t^8), not merely O(t^6).

T5. For a connected unicyclic support graph and a fixed h with nonzero cycle circulation, precisely one of the following holds:

    (i) Delta(t)=d4 t^4+O(t^6), d4>0;
    (ii) Delta(t)=d8 t^8+O(t^10), d8>0;
    (iii) Delta(t)=d12 t^12+O(t^14), d12>0;
    (iv) Delta(t)=0 for every real t.

Case (iv) holds exactly when the support graph is a pure cycle, all diagonal entries of B are equal, and the positive edge weights of B are two-periodic around that cycle. For an odd cycle two-periodicity means all edge weights equal; for an even cycle two alternating positive weights are allowed. If a vertex is attached outside the cycle, case (i) holds. All three nonzero orders occur, as witnessed by the exact rational matrices and edge data in proofs/HIERARCHY.md. No leading order 6 or 10, or finite order above 12, occurs in this unicyclic setting. Zero circulation is the separate trivial gauge-equivalent case already covered by T3.

T6. For every integer m>=1 there exist B and h satisfying the assumptions above, of dimension 4m+2 with positive diagonal, such that

    rho(A(t h))-rho(B)-E(t h)
      = t^(4m) / [2((2m)!)^2] + O(t^(4m+2)).

The same exact defect function also has a connected zero-diagonal bipartite realization of dimension 8m+4. Thus every nonzero leading order 4m permitted by T4 occurs on connected finite graphs. Explicit rational constructions, including all weights, diagonals and edge twists, are given in proofs/ARBITRARY_ORDER.md; the dimensions are upper bounds, not asserted minimal.

T7. The dimension 4m+2 in T6 can be replaced by 2m+2, preserving the strictly positive leading coefficient 1/[2((2m)!)^2], with rational B, integer edge twists h and positive diagonal. A zero-diagonal connected bipartite realization of the same exact defect function then has dimension 4m+4. The explicit construction is in proofs/DIMENSION.md, Sections 1-2.

The upper bound 2m+2 is optimal within the following restricted class: B has a uniform Perron vector; V is partitioned into two nonempty cells; h=0 on every cross-cell edge; the zero vertex potential minimizes the nonlinear energy for every real t in a neighborhood of zero; and the local increments k_i(t)=u_i^(-2) sum_j c_ij[cosh(t h_ij)-1] are constant within each cell for all such t. Every member of this class with strictly positive leading defect of order 4m has at least 2m+2 vertices. This restricted optimality does not assert a global minimum among all B,h.

T8. Let N_m be the least n>=2 among all B,h satisfying the initial assumptions for which Delta(t)=rho(A(th))-rho(B)-E(th)=c t^(4m)+O(t^(4m+2)) with c>0. Then

    N_1=3, N_2=3, N_3=4.

For m>=4, the established general bounds are 4<=N_m<=2m+2; equality is not asserted. The zero-diagonal minimum dimension is not determined. Proof and the minimal three-vertex fourth-order witness are in proofs/DIMENSION.md, Section 4.

T9. If the connected off-diagonal support is unicyclic and all diagonal entries of B are the same nonnegative constant, then Delta(t) is either identically zero or has a strictly positive fourth-order leading term; orders eight and twelve do not occur in this subcase. For nonzero cycle circulation, the identically-zero case is precisely the pure-cycle two-periodic edge-weight case of T5.

Let Z_m be the least n among zero-diagonal B with connected bipartite off-diagonal support and strictly positive leading defect of order 4m. Then Z_1=4 and Z_2=5, while 5<=Z_3<=8. A five-vertex K_(2,3) witness has Delta(t)=(5/512)t^8+O(t^10). Definitions, exact matrices through rational conductances, and proofs are in proofs/ZERO_DIAGONAL.md. These bipartite minima do not settle the minimum over all zero-diagonal, possibly nonbipartite, graphs.

Research scope: full finite-dimensional candidate proofs of T1-T9, exact examples, and reproducible author checks. The existing variational principle, matrix-balancing theory and ordinary fourth-order perturbation machinery are acknowledged as known antecedents. The defect hierarchy, sharp unicyclic classification, arbitrary-order construction, and dimension refinements are the current research focus; their priority remains unestablished. No claim of journal suitability, independent review, or formal verification is made.

Initial sources: Lee Altenberg, arXiv:1912.12771 (2019), https://arxiv.org/html/1912.12771; Canonical Structure and Orthogonality of Forces and Currents in Irreversible Markov Chains, https://pmc.ncbi.nlm.nih.gov/articles/PMC6566214/; Pietzonka, Barato, Seifert (2016), https://doi.org/10.1103/PhysRevE.93.052145. These motivate comparison and are not assumptions substituting for the proposed proofs.
