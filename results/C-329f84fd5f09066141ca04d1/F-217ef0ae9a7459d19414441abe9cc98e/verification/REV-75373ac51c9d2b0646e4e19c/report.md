# Independent paper and reduction review

Decision: PASS for the paper/reduction track. This is not a substitute for independent numerical execution review. Fresh context: only this request, its sealed materials, local workflow rules, and primary bibliographic sources were consulted; no author conversations or earlier review reports were read.

## Exact implication

Splitting a word by its used alphabet gives W(n,K)=sum binom(K,k) A(n,k), including n=0 and K=0. Inversion is valid separately for each n, and summing layers gives the total. If equal totals through eleven are assumed, the submitted finite separating certificate excludes different listed classes. Within one class, published word equivalence holds for every n,K, so inversion yields every layer. Numerical agreement is never the source of an all-length equivalence.

## Literature and coverage

The primary JM PDF was obtained from https://www.combinatorics.org/ojs/index.php/eljc/article/download/v16i1r58/pdf/ after the DOI endpoint failed. Section 1.1 (page 2) defines equivalence for all n,k and gives reversal/complement and the three length-three classes. Section 1.4 (pages 3-4) states completeness of the bijections plus these symmetries through size six. Appendix A (page 7), Tables 1-3, lists nontrivial rows only; omitted rows are individual symmetry orbits. The author table https://math.haifa.ac.il/toufik/enumerative/tablewords456.html supplies all representatives. The extracted nontrivial length-four and length-five rows match Appendix A. The only nonsymmetric binary length-six merger is 111112/111121/111211 in Table 3. Thus it is essential to include the singleton symmetry rows and 111111; the supplied data does so. The binary universe has 62 surjective two-letter words plus 111111, hence 63, not 64. Host alphabets in the binary-pattern case are unrestricted.

The coverage checker builds the entire packed pattern universe, expands each row under reversal and rank complement, checks union and disjoint cardinalities, and checks 75/16, 541/116, and 63/18 pattern/class totals. Its submitted coverage output reports precisely these values and the complete collision list. Small lengths are covered by the cited three classes and the explicit distinguishing counts. This review inspected the checker and its output but did not execute it.

## Algorithms, rederived

For packed hosts the final letter is either still present after deletion or is its unique occurrence. The former case has k choices, and the latter has k possible ranks to reinsert, giving F(n,k)=k(F(n-1,k)+F(n-1,k-1)). Census enumerates each surjection once; forcing unseen letters when remaining slots equal missing letters removes exactly impossible branches. Position combinations and standardization are correct. Epoch stamping counts a host once per contained pattern. Its population fits the signed integer stamp range for n=8,9.

Upward expansion is complete by deleting a position outside a chosen occurrence. The deleted letter either remains, giving existing-value insertion, or vanishes, giving fresh-rank insertion. Both preserve containment. The seed at length m is exactly the packed pattern. The bound k<=b+n-m follows from the at most n-m other positions. HashSet compares exact word encodings. The ascending k loop releases previous[k-1] only after its last use. Four-bit fields and 64-bit words suffice through eleven. The BinaryTail and ShadowPairs variants preserve these invariants.

For Joint, aMin is the smallest already repeated letter. cand[d] is the smallest a realizing a,a,d; a smaller a dominates all larger a for either final test. A second d completes a,a,d,d. For 11223, the least completed d suffices; for 11332, the union of open integer intervals (a,d) suffices. The mask subtraction sets exactly those interval bits. Suffix tests precede four-letter updates, which precede three-letter updates and the repeated-letter update, so positions cannot be reused. Completion[left,miss] counts suffixes using every missing letter and is independent of the particular missing labels. Early aggregation occurs only after both occurrences are permanent. Skipping k<3 and k>N-2 is justified by required distinct letters and the two repeated pairs.

## Finite certificate and limits

The baseline census separates length-four classes except 1223/1332, and length-five classes except the five pairs listed in argument.md. The corresponding submitted separating differences are 4 at length nine and 8,-20,6,-4,-12 at the stated lengths ten or eleven. For binary length six the two residual differences at eleven are -1 and 1. The coverage checker cross-checks complete baseline pattern coverage, class constancy, exact tie sets, receipt integrity, and overlapping counts from the shadow and joint procedures. These checks support the finite reduction; hashes alone cannot certify arithmetic.

No mathematical defect was found in the full stated reduction. Numerical execution independence remains the responsibility of the separate computation review. This report does not claim to have rerun exhaustive searches, verified resource receipts independently, proved the unrestricted length-six conjecture, or certified novelty.
