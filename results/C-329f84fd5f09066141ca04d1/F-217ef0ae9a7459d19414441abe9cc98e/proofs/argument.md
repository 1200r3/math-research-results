# Proof and reproducibility

For fixed n, split a word on [K] according to its used alphabet. Each subset of size k admits an increasing relabelling from [k], preserving all occurrences. Thus W_p(n,K)=sum_{k=0}^K binom(K,k) A_p(n,k). Binomial inversion proves (2) iff (3), and (2) implies (1). It remains to show that different word-Wilf classes have unequal totals at some n<=11.

Jelínek and Mansour (2009), §§1.1, 1.4 and Appendix A, establish the word-Wilf classes for these sizes. Use their table of representatives and close each row under reversal and rank complement. These operations preserve avoidance over every fixed alphabet. The distributed table extraction gives disjoint sets covering all 75 length-four, 541 length-five, and 63 at-most-binary length-six patterns. There are respectively 16, 116, and 18 word-Wilf classes in those sets. For m=1 there is only one pattern. For m=2 the classes are {11} and {12,21}, with n=3 totals 6 and 4. For m=3 the known classes consist of patterns of maxima 1, 2 and 3, with n=4 totals 66, 60 and 56. These small counts are also checked directly.

For m=4, enumerate all packed hosts of length 8. The sole collision among the 16 class representatives is 1223 and 1332, with common total 394884. Their totals at n=9 are 4472716 and 4472712. For m=5, enumerate all packed hosts of length 9. The only cross-class collisions are in the following table. For m=6 restricted to patterns with maximum at most two, compare the exact total vectors for n=6,7,8,9,10. Only the last two pairs in the table have coinciding vectors. The left-to-right order in every row matches the order of the two reported counts.

| m | class representatives | separating n | A_p(n) | A_q(n) |
|---|---|---:|---:|---:|
| 4 | 1223, 1332 | 9 | 4472716 | 4472712 |
| 5 | 11212, 12121 | 10 | 98890988 | 98890980 |
| 5 | 11223, 11332 | 11 | 1445533180 | 1445533200 |
| 5 | 12123, 13232 | 10 | 93909363 | 93909357 |
| 5 | 12234, 12443 | 10 | 87548792 | 87548796 |
| 5 | 13442, 14233 | 10 | 87410614 | 87410626 |
| 6 | 112112, 121112 | 11 | 1616420895 | 1616420896 |
| 6 | 111212, 112121 | 11 | 1616424886 | 1616424885 |

## Exact computations

Census.cs enumerates every host over its actual alphabet [k], never expanding a prefix into a branch that cannot use all k values in the remaining positions. At every leaf it enumerates all increasing position selections of length m and records each distinct standardized pattern once. Each host and each selection has one enumeration path. The lookup computes a letter's standardized rank as one plus the number of smaller distinct selected values. The observed host population agrees with F(n,k)=k(F(n-1,k)+F(n-1,k-1)), with F(0,0)=1: deletion of the final letter either leaves a surjection or removes its only occurrence. Subtracting containing counts from the host population gives total avoidance. The compiler and runner are recorded; the small coverage checker checks all class expansions, receipt hashes and exact comparisons.

ShadowPairs.cs, ShortShadows.cs and BinaryTail.cs count containing hosts of one pattern by upward expansion. Every new word is obtained by inserting either one existing value, or one fresh rank with all old values at least that rank incremented. The recurrence is complete: in any longer containing word choose an occurrence and delete a position outside it, then standardize. Conversely both types of insertion retain the old occurrence. Per-layer hash sets store the packed words themselves, so exact deduplication, not a hash collision assumption, is used. Four-bit fields are sufficient because the largest rank is at most 11. A layer with a value set larger than b+n-m cannot contain a pattern of maximum b and length m. The runner uses that upper bound, and subtracts containing counts from the full layer populations.

Joint.cs computes the single length-eleven exception 11223/11332 by a different, streaming prefix procedure. Write their witnesses as (a,a,d,d,x), with a<d<x or a<x<d, respectively. For each d maintain the least a<d for which the prefix already contains (a,a,d); the least value repeated twice so far suffices to update this on reading d. When another d is read, the old three-letter prefix state yields (a,a,d,d); it opens the suffix values larger than d for the first pattern, and those strictly between a and d for the second. Thus a minimum completed d and a bit mask of intervals describe all valid final letters. The automaton tests the current letter as a suffix before updating four-letter states, updates four-letter states before updating three-letter states, and updates the repeated-value minimum last. This prevents reuse of a position. If both patterns have occurred, the number of packed completions can be added to both counts without enumeration: with t slots and u unseen letters the number is S(t,u)=(k-u)S(t-1,u)+u S(t-1,u-1), with S(0,0)=1 and S(0,u>0)=0. Its length-nine and length-ten totals agree with the independent shadow procedure.

Every cross-class tie is therefore resolved by an explicit count at length <=11. Equality through 11 forces membership in the same known word-Wilf class; that membership is an all-length result from the published word equivalences. No all-length equivalence is inferred from numerical agreement alone.