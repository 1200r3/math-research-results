# Sources, prior work and citation

## Original problem and known results

Krystian Gajdzica, *The Turán and Laguerre inequalities for quasi-polynomial-like functions*, **Research in Number Theory** 10, article 46 (2024), published 21 April 2024. DOI: [10.1007/s40993-024-00532-7](https://doi.org/10.1007/s40993-024-00532-7). Preprint: [arXiv:2310.13814v1](https://arxiv.org/abs/2310.13814v1), 20 October 2023. These are versions of the same work, not two independent results.

- Theorems 4.3–4.4: earlier sufficient criteria and the smooth leading coefficient. These are prior work, not claimed as this repository's discoveries.
- Examples 4.5–4.6: periodic examples, including four colored parts of size one and one part of size 300. That special case is known.
- Problem 5.6 asks for stronger criteria for quasi-polynomial-like functions. QP01 treats the explicitly specified two-parameter partition family, not the entire broader problem.
- The source Example 4.6 writes residue 297 modulo 300, whereas our exact definitions use m dividing n+2d. We preserve the source's wording and our exact theorem separately; neither a silently edited quotation nor an unverified claim of correction priority is made.

[Paper bibliography in BibTeX](paper/refs.bib) · [Proof architecture](proofs/LEAN_MAIN_PROOFS_QP01.md)

## Related work checked during publication preparation

K. Gajdzica, B. Heim, M. Neuhauser and B. Żmija, *Submultiplicative polynomials in combinatorics*, **The Ramanujan Journal** 71, article 17 (2026), published 26 September 2026. [DOI 10.1007/s11139-026-01475-6](https://doi.org/10.1007/s11139-026-01475-6). Its abstract and Theorems 1.1/1.3 concern recursively defined polynomial sequences and submultiplicativity P_a P_b≥P_(a+b); this is a different inequality and parameter setting from the fixed-family, higher-order discrete Laguerre classification here. This is a limited comparison, not an exhaustive novelty certificate.

Publication-preparation access date: 5 November 2026 (Asia/Shanghai). The original DOI/arXiv pages and related publisher article were re-opened; exact-keyword queries included Gajdzica/Laguerre/classification/partitions, colored partition/threshold, and GitHub Laguerre/quasi-polynomial. Existing documented search limitations remain. The novelty classification is partial_known and worldwide priority remains unclear.

## Cite this project

Author: **1200**. Title: *Discrete Laguerre inequalities for a colored partition family*. Public research artifact and preprint, not a claim of journal acceptance. Cite the exact release and commit shown by the repository's verification record. This project has no registered DOI; the Gajdzica DOI above identifies the source paper, not our result.

Repository: [1200r3/math-research-results](https://github.com/1200r3/math-research-results). Machine-readable citation: [CITATION.cff](../../CITATION.cff). Code and Lean: MIT. Paper and authored prose: CC BY 4.0. Third-party sources and dependencies retain their own licenses.
