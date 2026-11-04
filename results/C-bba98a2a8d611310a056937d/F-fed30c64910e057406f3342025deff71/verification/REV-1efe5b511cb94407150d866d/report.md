# QP01 独立形式化审计报告

结论：**PASS**。本结论绑定请求 `REQ-ec89d9e89db72575d3726958`、成果包 `PKG-cceef00d1439606f40e59dfd`、命题 `C-bba98a2a8d611310a056937d` revision 1，封印 `45f5f6a50e07a5dca44e0bf9eda779b9fc63632186ca3f5f3c22110e1725246f`。有效执行为 `CHECK-a647218bbe7d06bb2a9763db`，执行记录哈希 `253da5d126f12dcda4bafbc050204272264d6237b1b3597d4a67defd14ec032b`。

审稿人：`qp01-public-formal-auditor`；上下文：`qp01-public-formal-context-20261105`；模型：`UNKNOWN`。本上下文与证明作者及 statement 审稿者不同，未编写、修改作者证明，未复用另一审稿者报告。此前在本同一审稿上下文所做的是静态准备，不是另一份独立审稿，也未在成功执行前给出 PASS。本正式意见在最新执行成功及正式请求生成后完成。

## FA-01：请求、材料及执行绑定（通过）

独立只读核验程序 `verify_review_evidence.py` 实际重新校验了请求所列 557 份材料的大小及 SHA-256，并重新计算 execution-checks 三个目录的原生 inventory digest，全部与请求相符。所有 result.json 的包、命题及封印均匹配；各步日志 SHA-256 与结果、逐作业回执的退出码及超时标记一致。核验结果见 `evidence-verification.json`。

已逐项检查三次主库执行，而不是仅使用作者历史日志：

| 执行 | 实际结果 | 审计处理 |
|---|---|---|
| CHECK-996ed227a0209df1317f89a1 | GitHub 连接失败，无法获取锁定 Mathlib，build 退出 1 | 保留失败，不作证明成功依据 |
| CHECK-87cc39fb9925fa71c554f407 | 依赖源码构建达到约 800 个任务后总时限耗尽；timed_out=true | 保留失败，不解读为数学反例或内核拒绝 |
| CHECK-a647218bbe7d06bb2a9763db | build、公理检查、fresh checker 三步均退出 0，均未超时；依赖稳定性终检成功 | 本次 PASS 绑定此最新成功记录 |

后两份失败记录不是被删除或改写，而是由成功的完整后续执行消解其环境/资源障碍。

## FA-02：完整目标与证明连接（通过）

原 `TargetStatements.lean` 的两个目标是 `PartitionLaguerre.mainClassification` 和 `PartitionLaguerre.aboveThresholdFailure`。新定理分别为：

- `MainClassification.lean` 的 `PartitionLaguerre.main_classification_proved : mainClassification`；
- `ConcreteLeadingCoefficient.lean` 的 `PartitionLaguerre.above_threshold_failure_proved : aboveThresholdFailure`。

两者是无额外参数/假设的证明常量，不是原 Prop 的定义本身。AuditFinalQP01.lean 第 49、50 行的两个 example 直接填充两个原 Prop；日志实际编译并打印这两个目标。虽原 collector 的 theorem 字段仅指定分类定理，完整 build 中 AuditFinalQP01 第 212–213、368–369 行的类型和公理输出，以及对整个 AuditFinalQP01 的 fresh 重放，同时覆盖负性定理。因此没有把单一引理的成功升级成完整主结果。

检查范围覆盖自然数 d,m≥2、共同自然数尾界 N、所有 n≥N 与 1≤j≤d；负性目标覆盖所有充分大且 m 整除 n+2d 的点。partitionCount 是原实际有限二项式和，laguerre 的符号、范围及两个序列下标与精确目标一致；criticalIndex 使用自然数中央二项式除以 2，临界消去证明实际使用其二整除性。d=1 不被纳入目标。

直接静态追踪以下闭合链：ConcretePartitionModel 从 Bernoulli 有限幂和、Pochhammer 构造实际剩余类多项式并证明原有限和表示；PolynomialPart/PolynomialPartDegree 给出共同多项式部分及实际次数首项；ConcreteLeadingCoefficient/ConcretePositiveBranches 证明低阶、非临界正性和超阈值负性；MainReduction 以异常类无界证明分类必要性。奇数临界分支在 CriticalCancellations 中消去实际高两项，MainClassification 将实际 2d−2 系数识别为 criticalBetaQ，再由 CriticalBetaRational/CriticalPositivity 得到严格正性。没有把表示、正性或目标作为未填充额外前提。

PolynomialBounds 的正负求值界、ResidueDefinitions 的 coefficientBound/uniformResidueBound 以及 MainReduction 的连接实际提供有限显式尾界；不是仅假设“某多项式最终有符号”。自然数减法只在真实求和范围内转换，原模类标签在有理变量平移时保留。

## FA-03：锁定版本、实际构建及公理（通过）

lean-toolchain 为 Lean 4.35.0，实际 Lake/leanchecker 路径属于该工具链。Mathlib 锁定 commit `56a005855ea17e0b0958f73ec801ae140b0a1679`；八个传递依赖也有固定 commit，执行中的映射与全部九项锁定版本一致。

最新 step-1.log 显示全部 **47 个项目 .lean 模块**均为 Built，包含 43 个证明/定义模块和 4 个审计模块，结尾为 `Build completed successfully (2478 jobs).`。核验程序将材料中每一个模块名与实际 Built 行逐项比较，没有遗漏。原 collector 源码证明只将封存 lean 文件复制到新临时目录；本项目对象未被复用。依赖对象缓存复用的边界见下一节。

检查 build 日志中全部 **454 次公理集合报告**，均为 propext、Classical.choice、Quot.sound 的子集，没有 sorryAx。两个最终目标各自的实际报告均恰为 `[propext, Classical.choice, Quot.sound]`。step-2.log 再次确认分类定理类型及同一公理集合。全项目禁用构造文本检索未发现有效 sorry、admit、自定义 axiom、unsafe、implemented_by、extern、native_decide、run_tac 或自定义 elab；注释与 #print axioms 不作为禁用构造。没有导入外部 QP01 已证结论再冒充本次新证明。

step-3 的实际 argv 为同一工具链 `leanchecker.exe --fresh AuditFinalQP01`，其日志为空且 SHA-256 为合法空文件摘要，作业回执退出 0、timed_out=false。空日志不被误写成缺失日志。已读工具链 LeanChecker.lean：replayFromFresh 导入目标及传递依赖后，将全部常量在空环境重放，所以覆盖两项最终证明与依赖常量。

日志有 123 条警告，内容为模块系统导入建议、弃用导入/语法、未用 simp 参数及 tactic linter 等；未出现构建错误或证明占位。这些维护提示不阻断本次数学目标验收，未修改原包来隐藏警告。

## FA-04：依赖缓存适配器及可信边界（通过，须保留说明）

审查了执行目录内实际存档的 collector-dependency-adapter.py，并比对其与实际 ops 文件的哈希。它没有替换原 execution.check_lean 的三步验证、成功判定、日志收集或数据库登记；只在调用真实 Lake 时添加 `--packages=... --old --no-cache`，实际 argv 已完整留档。`--old` 会忽略传递依赖变更，故本次不能声称 Mathlib 全部从源码重新构建。包内 QP01 模块则在无本项目构建对象的新目录真实编译。

对九项依赖的 **9971 个 Lean/config 文件**，适配器按官方 GitHub 精确 commit 树逐项核验 Git blob 和 SHA-256。本审稿程序再次读取隔离副本的全部这些文件，独立重算 SHA-256 及 Git blob，与执行证据相符。额外可导入源码和无上游对应源的对象拒绝检查实际通过。

先前 Plausible.lean 差异为 CRLF 与 LF；官方 LF 字节的 Git blob 匹配，修订仅在隔离依赖副本中进行。最新成功执行的 normalization 列表为空，表示该次核验开始时已为官方字节，不能写成该次又执行了规范化。安装源 SHA 另存于逐文件记录，可审计历史差异。Mathlib 的历史弱栈大小配置恢复有独立前后哈希，数学 Lean 源未因此改写，原共享安装未变。

准备阶段发现的两项适配器缺陷已在本次执行前修复：checker 检测改用参数 basename，完整纳入 .olean、.olean.server、.olean.private，并比较运行前后路径集合与逐对象 SHA-256。最终 dependency-object-stability.json 确认 **27147** 个对象部分集合与内容不变，此文件也包含在绑定的执行目录摘要中。

缓存来自历史本机构建；STATUS.md 仅是来源/进度线索，本审稿未把它当作本次成功构建证据，也没有从它推断历史完整成功。内核 fresh 重放与当前源码精确核验、对象稳定性共同支持本次受信任本机依赖缓存的使用；它们不构成缓存定义与源码的一般独立编译等价证明。STANDARD 要求实际干净项目构建、锁定依赖、允许公理及 fresh 成功，没有要求每个第三方依赖必须重新从源码构建。按该明确范围，本次证据足以通过，而不能包装成第三方库全部冷构建。

## 限制及最终判断

本审查是 formal_audit，完整覆盖两项精确主目标及其有限显式界的形式连接；不是独立纸面全推导、双盲 read-back、查新或全球优先权认证。Lean 的具体剩余类构造与纸面部分分式展示公式不同，未声称逐字形式化所有展示公式、一般周期边界公式、任意分拆族或 d=1 分类。

leanchecker 是 Lean 自身内核重放，不是独立实现的外部证明核。缓存未全部从源码重编，校验依赖受信任本机工具链与上述记录。本审稿者没有额外重复构建或改写包/主库。

没有尚未关闭的验收问题。基于独立静态审查及最新成功实际执行，本次正式结论为 **PASS，checked_entire_claim=true**。
