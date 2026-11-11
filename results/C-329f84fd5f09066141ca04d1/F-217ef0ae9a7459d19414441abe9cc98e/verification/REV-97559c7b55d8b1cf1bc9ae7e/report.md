# Independent computational review

Request REQ-33953b3924c5f107ebe1e15c; context CTX-0869d529259cd62f384a22f1; reviewer c86-astra-compute. This continues the original fresh context and does not claim an additional reviewer.

## New independent method
Independent.cs was written in this review. It generates every set partition of eleven positions exactly once as a restricted-growth string. Labeling its k blocks by a permutation of ranks 1 through k enumerates packed words exactly once. The actual partition total was 678570.

For 11223 and 11332, each five-position subsequence with block form (a,a,d,d,x), all three blocks different, contributes a triple. Deduplicated triples capture exactly all possible occurrences. Only blocks in triples matter to avoidance. If h such blocks exist, each relative ordering of them extends to k!/h! orderings of all blocks. The program enumerates these h! orders and tests a<d<x and a<x<d respectively. Empty triple sets correctly contribute k! to both avoidance totals.

For each of four binary patterns, and each ordered pair of distinct blocks (u,v), a greedy subsequence scan decides whether its shape occurs with 1 mapped to u and 2 to v. If so, avoiding it requires v to have smaller rank than u. The program constructs all such precedence constraints and counts their linear extensions by exact subset DP: append a block only when all its predecessors have been appended. Cycles automatically yield zero. All blocks, including unconstrained ones, occur in this DP, so no labeling multiplicities are omitted.

This method differs from both submitted upward insertion and prefix-state recognizers. All arithmetic uses signed 64-bit integers; per-partition DP counts are at most 11!, and accumulated totals at most the length-eleven ordered Bell number, both safely in range. No hash-based probabilistic counting occurs.

Observed independent n=11 totals:
11223: 1445533180; 11332: 1445533200.
112112: 1616420895; 121112: 1616420896.
111212: 1616424886; 112121: 1616424885.
All six match the sealed evidence. The executable checks these totals and the number of partitions and throws on mismatch.

## Audit inherited from preceding reassessment
All 28 sealed file digests matched. All five submitted C# algorithms and coverage checker were inspected. Census generation is exhaustive over surjections, its position selections exhaust all subsequences, rank lookup preserves strict inequalities and equalities, and stamps avoid multiple counting per host. Stamps at n<=9 cannot overflow. Upward insertion is exhaustive by deleting a position outside an occurrence and packing; exact HashSet equality deduplicates encoded words. Four-bit fields are sufficient for every submitted alphabet bound. Joint's state updates run in decreasing subsequence length, preventing position reuse; its completion recurrence counts packed extensions exactly.

The preceding successful job freshly recompiled and reran BinaryTail and Joint and executed the coverage checker. The checker verified complete disjoint partitions of 75, 541 and 63 patterns into 16, 116 and 18 submitted classes, all census coverage, collision lists, separating witnesses, binary continuation consistency, and the m=2,3 direct counts. All submitted receipt hashes matched. Published equivalences within rows belong to the separate paper reduction audit; numerical agreement alone is not used as an all-length equivalence proof.

## Final execution and decision
PASS for this request's computational scope. checked_entire_claim=true means that the entire finite computational component supporting the stated claim was reviewed; it does not replace the separate literature/reduction reviewer.

Job JOB-3df90d883698a5154c8efaf3 completed successfully, returncode 0, no timeout. Log SHA-256 2aeb959321612d87831b9fe4ea8dd0700bdd659a786e3aac278bfdb1ce6e8aad. Single thread, 1 GB reserved, 240-second limit; admission memory is not a hard OS limit. Independent.cs SHA-256 2daf94f958e2c6af4f117bda7260adfc04f17ad1be742132e9b76851a314c9ee.

After the independent algorithm, all Census, ShadowPairs and ShortShadows computations were freshly compiled and executed. Every submitted numeric output record matched: 616 census records, 88 shadow records, 102 short records. Thus all submitted finite-count algorithms have now been rerun across the preceding and current jobs, and all three critical pairs have additionally been recomputed by mathematically different algorithms. No unresolved computational discrepancy remains.

The earlier INCONCLUSIVE reports are preserved as historical partial reviews. No registry edits or publication actions were taken. Initial Windows default startup failed; narrowly elevated execution subsequently worked. No local absolute paths appear in the report or computation logs.
