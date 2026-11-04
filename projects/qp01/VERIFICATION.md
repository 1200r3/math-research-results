# Verification and release scope

Formal acceptance: `F-fed30c64910e057406f3342025deff71` for claim `C-bba98a2a8d611310a056937d` revision 1, licensed package `PKG-cceef00d1439606f40e59dfd`, SHA-256 `45f5f6a50e07a5dca44e0bf9eda779b9fc63632186ca3f5f3c22110e1725246f`.

The two exact targets are `PartitionLaguerre.mainClassification` and `PartitionLaguerre.aboveThresholdFailure`. The complete claim includes the computable finite threshold construction; broader paper display identities are not all formalized verbatim.

- Clean project build, target axiom audit and `leanchecker --fresh AuditFinalQP01`: CHECK-a647218bbe7d06bb2a9763db, all actual command exits zero, no timeout.
- Two different independent model contexts: statement review REV-9624ea3509681b98501b1a9b and formal audit REV-1efe5b511cb94407150d866d, both PASS and complete for this claim.
- 47 project modules (43 proof/definition modules and four audits), both original Prop goals directly filled. The author audit selects 177 named theorems; repeated log reports are not extra research results.
- Nine third-party dependencies are locked; 9,971 source/config files were checked against exact upstream Git blobs. Only CRLF line endings and the historical local Windows stack-size build setting were restored in an isolated dependency copy.
- 27,147 dependency object parts were stable across the run. Only third-party dependency caches were reused; QP01 itself was built from a directory with no project objects. This does not claim a full Mathlib source rebuild.
- Fresh replay is Lean's own kernel replay of all imported constants, not an independently implemented external kernel. Model-context independence is a recorded declaration, not a proof of absence of shared blind spots.

[Immutable accepted artifacts](../../results/C-bba98a2a8d611310a056937d/F-fed30c64910e057406f3342025deff71) · [Actual verification evidence](../../results/C-bba98a2a8d611310a056937d/F-fed30c64910e057406f3342025deff71/verification)

The PDF was prepared on 30 October and preserves its earlier pending-review wording. The versioned acceptance records linked here describe the later completed acceptance on 5 November 2026 (Asia/Shanghai). Neither the PDF nor these checks imply journal peer review, acceptance or worldwide priority. The original novelty record remains dated 29 October; the later limited source recheck is documented in [REFERENCES](REFERENCES.md).
