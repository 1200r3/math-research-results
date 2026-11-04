# QP01 最终主证明复验（作者自查）

时间：2026-10-30T04:19:56.159889+08:00。项目P-e0470a3e0dd8f6277bfad9a0；尝试A-886620b7af8e1a5127275dd8；命题C-bba98a2a8d611310a056937d revision 1；父包PKG-26e91aeda5851f6f64892705。

## 结论与范围

两个原始Prop现在都有无条件Lean证明：`main_classification_proved : mainClassification`及`above_threshold_failure_proved : aboveThresholdFailure`。原Prop定义、statement.md、原十个证明源码及旧审稿保持不变；不是把定义的编译成功当作证明。严格范围为d,m≥2的指定分拆族，以及1≤j≤d；d=1和一般分拆族不在其中。

| 验证目标 | 结果 | 实际连接 |
|---|---|---|
| 两个原Prop的直接填充 | 通过 | AuditFinalQP01中的两个example，未更改原定义 |
| 精确分拆有限和与实际F_r | 通过 | ConcretePartitionModel；不是额外模型假设 |
| 共同P+b、次数与首项 | 通过 | PolynomialPart、PolynomialPartDegree |
| n+2d偏移及实际周期边界项 | 通过 | PartitionDifference、PeriodicDifference、ConcreteLeadingCoefficient |
| 全部低阶、偶数d及奇数严格低于阈值的正性 | 通过 | ConcretePositiveBranches |
| aboveThresholdFailure | 通过 | above_threshold_failure_proved；奇数超过阈值的整除类严格负性 |
| 奇数临界中心化、二次下项、下一偶数矩 | 通过 | CenteredSecondCoefficient、NextLaguerreMoment |
| 实际周期Green函数和B1、B2 | 通过 | CriticalGreenIdentification、CriticalPeriodicMoments |
| 临界q及q-1项消去，实际q-2项识别 | 通过 | CriticalCancellations、MainClassification |
| mainClassification | 通过 | main_classification_proved；完整指定二参数范围 |
| 显式最终界 | 通过 | uniformResidueBound作用于具体F_r；自然数输入的有理多项式界 |
| 依赖锁 | 通过 | 9项精确Git版本，Lean4.35.0；本地路径覆盖单列 |
| 全量构建、公理和fresh | 通过 | 43个证明模块、177项命名目标；空输出重建与重放对象逐字节一致 |

## 可复核执行证据

全量构建、类型与公理、内核重放分别见`final-qp01-v1-build.log`、`final-qp01-v1-axioms.log`、`final-qp01-v1-fresh.log`。全部47个本项目目标包括43个证明模块、3个旧诊断模块和新的AuditFinalQP01。177项命名目标的完整类型在axioms.log，逐项源码行号、公理集合与覆盖表在`final-theorem-verification-table.json`。全部公理是propext、Classical.choice、Quot.sound的子集；无新增公理或占位证明。fresh重放覆盖目标及全部导入常量，不能把177这个选定审计数当作导入常量总数。

第一轮构建使用既有有效输出；为消除这一限制，另在初始不存在的`.lake/cold-qp01-main`中重建所有47个本项目目标。冷构建与公理日志是`final-cold-qp01-v1-build.log`、`final-cold-qp01-v1-axioms.log`。47个冷构建olean与已成功fresh重放的对象逐字节相同，源码和锁定配置前后哈希不变，因此无需对相同字节再次重放。依赖使用已校验的锁定缓存，不宣称从空缓存重编整个mathlib。

全部命令、耗时、退出码、日志哈希在两个`*-execution.json`；外层run-job回执均returncode=0且timed_out=false。总证据索引为`evidence/qp01-verification/final-main-proof-closure.json`。工具使用锁定Lean4.35.0，工具二进制哈希、43份源码与配置哈希见`final-qp01-v1-input.json`。

此前main-progress-a合并作业在fresh阶段超时，不能计为成功；后续main-progress-b独立重放才成功。中间90条的89+1补查如实保留。失败编译中错误恢复打印的sorryAx不是成功证明证据。当前结论只依赖最终全量通过且哈希稳定的记录，不删除任何失败日志。

## 数学衔接与未逐字形式化的范围

完整作者推导见`proofs/LEAN_MAIN_PROOFS_QP01.md`。实际F_r由Bernoulli有限求和构造，P取F_0；与纸面规范化公共主部可以相差常数。所有主结论都从原有限分拆和推出，没有假设实际周期模型或临界首项符号。奇数临界分支先证明实际q及q-1项消去，再识别q-2项为criticalBetaQ，并与已有实数criticalBeta正性连接。

纸面(4.4)的u_h递推、复根部分分式、形式留数展示式尚未逐字形式化；一般实系数多项式对所有实数的界、任意ell周期边界通式、little-o推广也不在这两项Prop的证明范围。使用等价的具体F_r构造及有限显式界，须由独立statement核对确认其与整份纸面命题的对应范围；本报告不声称纸面每条附加公式均已形式化。

## 查新与独立验收

查新沿用本轮实际五类渠道复核及原始返回，见`research/NOVELTY_RECHECK_QP01.md`。已知充分条件、平滑系数与特例已归于文献；指定族完整二参数分类、一般周期边界及奇数临界结论未在所读来源中确认，但索引、引用和订阅访问存在缺口。新颖性仍partial_known，全球优先权unclear，不承诺全球首次。

这是同一研究者上下文的证明与复验，不是独立审查，也未改变主库formal状态。新包尚未入hub，官方check-lean为not_registered_in_hub。协调员须对新包哈希安排不同全新上下文的完整statement核对与formal_audit，并在主库保存规定执行证据；旧包审稿不得替代。

## 全模块覆盖

下表数量为本模块声明、纳入最终命名类型与公理审计的定理数；零表示仅含定义，不表示未构建。所有模块及其导入常量均在最终fresh范围中。

| 模块 | 命名定理数 | 全量构建/审计/重放 |
|---|---:|---|
| `CenteredPolynomial` | 5 | 通过 |
| `CenteredSecondCoefficient` | 5 | 通过 |
| `ConcreteLeadingCoefficient` | 8 | 通过 |
| `ConcretePartitionModel` | 8 | 通过 |
| `ConcretePositiveBranches` | 8 | 通过 |
| `CriticalBetaRational` | 2 | 通过 |
| `CriticalBinomialIdentities` | 4 | 通过 |
| `CriticalCancellations` | 4 | 通过 |
| `CriticalCenteredTransform` | 6 | 通过 |
| `CriticalCoefficientTools` | 4 | 通过 |
| `CriticalGreenIdentification` | 4 | 通过 |
| `CriticalPeriodicMoments` | 4 | 通过 |
| `CriticalPositivity` | 3 | 通过 |
| `CriticalReduction` | 4 | 通过 |
| `CriticalSmoothCoefficient` | 2 | 通过 |
| `CriticalSmoothMonomials` | 4 | 通过 |
| `CyclicDifference` | 10 | 通过 |
| `CyclicGreen` | 6 | 通过 |
| `DifferenceProduct` | 2 | 通过 |
| `LaguerreMoments` | 6 | 通过 |
| `LeadingSigns` | 1 | 通过 |
| `MainClassification` | 3 | 通过 |
| `MainReduction` | 7 | 通过 |
| `NextLaguerreMoment` | 6 | 通过 |
| `PartitionDefinitions` | 0 | 通过 |
| `PartitionDifference` | 2 | 通过 |
| `PartitionRecurrence` | 4 | 通过 |
| `PeriodicDifference` | 6 | 通过 |
| `PochhammerDifference` | 2 | 通过 |
| `PolynomialBounds` | 4 | 通过 |
| `PolynomialPart` | 3 | 通过 |
| `PolynomialPartDegree` | 6 | 通过 |
| `PolynomialTopCoefficients` | 4 | 通过 |
| `ResidueDefinitions` | 0 | 通过 |
| `ResidueEvaluation` | 2 | 通过 |
| `ResiduePolynomialExpansion` | 6 | 通过 |
| `ResidueTargets` | 0 | 通过 |
| `RootCancellation` | 1 | 通过 |
| `ShiftTopCoefficients` | 6 | 通过 |
| `SmoothMonomial` | 11 | 通过 |
| `SmoothPolynomial` | 4 | 通过 |
| `Statement` | 0 | 通过 |
| `TargetStatements` | 0 | 通过 |

合计43个证明模块、177项命名目标。逐目标明细见同目录`MAIN_PROOF_TARGET_MATRIX_QP01.md`及机器表。
