# Research progress and exact scope

Claim revision 5; delivery update 2026-11-01. The written T1-T9 proof is complete, with no currently identified substantive mathematical gap. Two fresh-context AI paper reviews passed the original r5 snapshot; formal fixed acceptance remains incomplete. Ten substantive research units are recorded in research/ROUNDS.md; later review and novelty follow-ups are recorded separately. See ../DELIVERY_README.md for the current delivery scope.

| Item | Current evidence | Limitation |
|---|---|---|
| T1 nonlinear bound and equality | FULL_PROOF Sections 1-3 | Known variational antecedent; author proof |
| T2 fourth-order defect | FULL_PROOF Sections 4-6 | Standard perturbation machinery; author proof |
| T3 unicyclic scalar reduction | FULL_PROOF Section 7 | Related current-fluctuation literature |
| T4 all-order local hierarchy | HIERARCHY Sections 1-2 | Local resolvent identity only |
| T5 sharp 4/8/12 classification | HIERARCHY Sections 3-4 | Connected unicyclic support, nonzero circulation |
| T6 realization of every order 4m | ARBITRARY_ORDER Sections 1-4 | Dimension upper bounds, not optimality claims |
| T7 smaller construction and two-cell optimality | DIMENSION Sections 1-3 | Restricted-class optimum, not a global optimum |
| T8 exact N1=3,N2=3,N3=4 | DIMENSION Section 4 | Global N_m for m>=4 remains open |
| T9 constant-diagonal rigidity and Z1=4,Z2=5 | ZERO_DIAGONAL | Z minima require bipartite support; Z3 only bounded by [5,8] |
| Orders 4,8,12 occur | Exact matrices and rational coefficients in both proof files | Same author derived and checked |
| Finite calculations | Successful job records and 80-digit results | No interval arithmetic; no general computational proof |
| Novelty | Original source comparisons through 2026-11-01; independent INCONCLUSIVE | T1-T4 known mechanisms; T5-T9 no equivalent complete prior found within documented scope; global priority unestablished |
| Formal verification | not_run | Mathlib not established locally; no main theorem proof |
| Independent paper review | Two fresh-context full T1-T9 PASS on PKG-e7489888f5d4be435d315a7d | AI paper reviews, not formal verification; subsequent normalization wording clarified; old PASS do not automatically transfer to a new package |
| Independent counterexample/boundary review | Requested but no response delivered | Not counted as PASS; fixed gate incomplete |
| Delivery integrity audit | 35 original code/evidence hashes unchanged; five successful latest run-log hashes verified | No new numerical rerun; package validation checks structure/hashes only |

No substantive mathematical gap is currently identified in the written candidate T1-T9 proof; the two full paper reviews support that assessment within their reported limits. This is not complete v2 fixed certification. Scope boundaries include connected finite simple support, nonnegative diagonal, fixed-parameter remainders, no uniform graph-family bounds, no isolated-equality classification away from zero, and no general global minimum dimension for m>=4. The two-cell restriction and the bipartite restriction are essential to their respective optimality claims.

The research problem was not silently weakened. Revisions 2,3,4,5 successively add T4-T5, T6, T7-T8, T9 without removing earlier conclusions. Previous statements/claim metadata and the sealed r3 package remain. Next mathematical questions are Z3 in [5,8] and global N_m for m>=4; priority and independent validation are separate open tasks.
