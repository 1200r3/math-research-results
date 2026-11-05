# QP01 — Discrete Laguerre inequalities for a colored partition family

**Paper byline: 1200 and GPT Astra (AI contributor).** Number theory / enumerative combinatorics / formal mathematics.

[Corrected paper PDF](paper/2026-11-05-correction/main.pdf) · [TeX](paper/2026-11-05-correction/main.tex) · [Erratum](ERRATUM-2026-11-05.md) · [Main Lean proof](lean/MainClassification.lean) · [Proof architecture](proofs/LEAN_MAIN_PROOFS_QP01.md)

## Abstract

For integers $d,m\ge2$, let $p_{d,m}(n)=[z^n](1-z)^{-2d}(1-z^m)^{-1}$ and
$T_j(f)(n)=\sum_{k=0}^{2j}(-1)^{k+j}\binom{2j}{k}f(n+k)f(n+2j-k)$.
The supplied proof establishes eventual strict positivity simultaneously for all $1\le j\le d$ exactly when $d$ is even, or $d$ is odd and $m\le1+\binom{2d}{d}/2$. Above the odd threshold, order $d$ is eventually negative on $m\mid n+2d$. At equality, two leading terms cancel and the next coefficient is positive.

## Progress by result

| Result | Accomplishment | Remaining limits |
|---|---|---|
| [Main classification](results/main-classification.md) | Full specified-family necessary-and-sufficient classification | Author proof supplied; independent statement and formal audits passed; repository formal acceptance recorded |
| [Negative residue class](results/negative-residue.md) | Above-threshold strict negativity on the specified class | Author proof supplied; independent statement and formal audits passed; repository formal acceptance recorded |
| [Odd critical equality](results/critical-equality.md) | Actual coefficient two degrees below is positive after cancellation | Supporting chain; not separately fixed |
| [Periodic boundary coefficient](results/periodic-boundary.md) | Paper identity with a cyclic-difference boundary contribution | General paper scope exceeds the two formal target Props |
| [Effective thresholds](results/effective-bound.md) | Computable finite bounds from rational residue polynomials | Formal natural/rational input scope; not every paper display formula is formalized verbatim |

作者已提交指定族的完整纸面与Lean候选证明；已通过主库独立陈述核对与形式化审计。这里没有声称攻克任意分拆族或原始广义问题。

The broader Gajdzica Problem 5.6 is not fully solved here. The strict classification excludes $d=1$. General real-coefficient bounds and unspecified little-o errors are outside the two formal Props. Prior smooth-coefficient results and the known $(d,m)=(2,300)$ example are credited. Novelty is `partial_known`; worldwide priority remains unclear. The numerical details of Example 4.6 are corrected in the linked erratum. The theorem and its accepted Lean proof are unchanged.

## Reproduction

Lean 4.35.0; Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; all transitive revisions are locked in `lean/lake-manifest.json`.

```sh
cd projects/qp01/lean
lake build
lake env lean AuditFinalQP01.lean
lake env leanchecker --fresh AuditFinalQP01
```

The author reports 43 proof modules, 177 selected named-theorem audits, clean project builds, and fresh replay. These are author execution records, not an assertion that this public repository has already passed independent acceptance or CI. Dependency cache reuse is not a full Mathlib source rebuild.

## Source and attribution

Gajdzica, *The Turan and Laguerre inequalities for quasi-polynomial-like functions*, Research in Number Theory 10 (2024), article 46, [DOI 10.1007/s40993-024-00532-7](https://doi.org/10.1007/s40993-024-00532-7), especially Problem 5.6, Theorems 4.3–4.4 and Examples 4.5–4.6.

The public license/attribution edition preserves the Lean source bytes of research package `PKG-841a68061cb2c3e57b1a97e3`. Public release and acceptance records will identify the exact final package/version; no immutable source was edited in place.

[Sources, prior work and how to cite](REFERENCES.md)

[中文成果摘要与未解决范围](SUMMARY.zh-CN.md)

[Current formal acceptance and immutable evidence](VERIFICATION.md)

A later source-bound clean build, axiom check, fresh replay, and two independent reviews have completed formal acceptance of the exact two targets. See [the current acceptance record](VERIFICATION.md). This is not a CI or journal-peer-review claim.

The [original paper](paper/main.pdf) remains available for citation to the original publication. For the corrected example, see the [exact arithmetic check](code/check_example46.py), the [Lean regression](lean/Example46Regression.lean), and [all 300 leading coefficients](results/example46-coefficients.json).
