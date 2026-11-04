# QP01 独立完整陈述对应性审查

日期：2026-11-04。结论：**PASS（仅 statement 轨道）**。

请求 REQ-eb15c587a712f8cb26370ad3；审稿标识 qp01-public-statement；上下文 qp01-public-statement-20261030；登记模型 UNKNOWN，原样保留。包 PKG-cceef00d1439606f40e59dfd；命题 C-bba98a2a8d611310a056937d revision 1；manifest SHA-256：45f5f6a50e07a5dca44e0bf9eda779b9fc63632186ca3f5f3c22110e1725246f。

本审查在独立子代理上下文进行；此前未参与作者研究、证明修改或同包审稿。收到协调者的任务与重点提示后，直接阅读 request 和材料。这是具有完整材料的对应性审查，不是仅看定义和声明的盲 read-back。fresh_context=true 表达上述事实，没有把同一上下文登记为多个审稿人。

## 1. 实际范围与绑定

已读根 AGENTS、LOCAL_WORKFLOW、STANDARD、04_verify 以及部署/复核/索引入口记录。逐项核对 statement.md 全文、proofs/qp_laguerre_draft.md 第1、3、4、5、6节与以下 Lean 定义及连接：PartitionDefinitions、TargetStatements、ConcretePartitionModel、PolynomialPart、ResidueDefinitions、ResidueTargets、ResidueEvaluation、PolynomialBounds、MainReduction、ConcreteLeadingCoefficient、ConcretePositiveBranches、CriticalReduction、CenteredPolynomial、CriticalCenteredTransform、CriticalCancellations、CriticalPositivity、CriticalBetaRational、MainClassification。

按 request.materials 全部557项重新计算 SHA-256，全部吻合，无缺失。哈希只确认绑定，不替代数学审查。

实际主目标是 PartitionLaguerre.mainClassification 和 PartitionLaguerre.aboveThresholdFailure；实际无条件入口分别为 MainClassification.lean 的 main_classification_proved 与 ConcreteLeadingCoefficient.lean 的 above_threshold_failure_proved。Statement.lean 的 formalStatement 只是复数代数恒等式，不是此次主目标，本结论没有拿它替代完整命题。

## 2. 定义、量词、范围（S1，已消解）

纸面整数 d,m≥2 与 Lean 自然数 d,m 加 2≤d、2≤m 等价。n 都为非负整数。partitionCount 中 range(n/m+1) 包括0至floor(n/m)。因 m>0 且 v≤n/m，mv≤n，n−m*v 的自然数减法等于普通减法；2d−1也无截断。该和由生成函数两个级数展开得到指定系数。

laguerre 的 k 在0至2j间，所以 2*j−k 非负，n+(2*j−k) 就是纸面 n+2j−k。符号、二项式、两因子完全一致。ℚ 到纸面实数的嵌入保序，严格 >0 和 <0 没有改变。

eventualPositiveThrough 的 N 同时适用于全部 n≥N 以及1≤j≤d，量词没有变成每个 j 各自存在 N。mainClassification 精确为偶 d，或奇 d 且 m≤criticalIndex d。d≥2 时中央二项式能被2整除，故 criticalIndex 的自然数除法恰是 1+C_d/2，没有取整误差。

aboveThresholdFailure 精确包括奇 d、m>criticalIndex、存在 N，以及全部 n≥N 且 m∣n+2d 的严格负性；不是仅给出一条子列存在性，也没有把余数条件错成 n+d。m>0 令该同余类无界；MainReduction 的 exceptional_class_unbounded 将它用于分类必要性。

## 3. Bernoulli 分支与纸面(4.4)–(4.5)（S2，已消解）

两种构造的完整分支多项式相同，但 P/b 的常数规范不同，不能直接说 concretePolynomialPart 就是纸面 P。

令 q=2d、k=q−1。Lean 用 descPochhammer/k! 表示 binom(r+mu+k,k)，用 Bernoulli/Faulhaber 多项式构造含端点0至t的有限和，再代 t=(X−r)/m。inclusive_power_sum_eval、inclusive_polynomial_sum_eval、step_binomial_polynomial_eval、concrete_partition_representation 将其连接到实际分拆和；特别0次幂的 u=0 项没有遗漏。因此 r<m、t∈ℕ 时，concreteResiduePolynomial(d,m,r)(r+mt)=p(d,m;r+mt)。

以下独立代数核对说明它为何也等于纸面公式，而不靠有限抽样：令 S(z)=1+…+z^(m−1)，U(y)=Σ_(h=0)^q u_h y^h。所给递推恰使 S(1−y)U(y)=1+y^(q+1)R(y)，其中 deg R≤m−2（零多项式照样成立）。故

1/((1−z)^(q+1)S(z)) − Σ_h u_h/(1−z)^(q+1−h) = −R(1−z)/S(z)。

右边又是 −(1−z)R(1−z)/(1−z^m)，分子次数≤m−1，所以系数从 n=0 起就是精确 m 周期序列。左侧第二项的系数是(4.4)的 P(n)。0≤r<m 时 p(r)=binom(r+q−1,q−1)，所以周期值恰为(4.5)的 b_r。纸面 F_r=P+b_r 与 Lean 分支在无限多个 X=r+mt 上相等，因此在 ℚ[X] 中相同。此论证覆盖全部参数域，不依赖接受复根部分分式公式，也不只是数值样例。

Lean 选 concretePolynomialPart=concreteResiduePolynomial(d,m,0)=纸面 P+b_0，concretePeriodicConstant(d,m,r)=纸面 b_r−b_0。相加仍是同一 F_r。本次结论及界都用完整 F_r，因此这个常数差异无碍。此等同关系是本报告的数学核对；没有声称 Lean 另有直接名为“等于纸面(4.4)”的定理。

## 4. 变换与显式界（S3，已消解）

residueTransform 逐项就是纸面 h_(j,r)：余数0至m−1、comp(X+C k)就是代入X+k、范围内的2j−k没有截断。represented_sequence 把其求值连接到原序列变换。

非零多项式的 natDegree/leadingCoeff 对应 K/c_K；lowerCoefficientMass 是 Σ_(i<K)|c_i|；coefficientBound 为1+Nat.ceil(S/|c_K|)。比值非负，Nat.ceil 就是所需上取整，常数非零多项式的 B=1。零多项式在 Lean 中因0/0=0而 B=1；uniformResidueBound 又显式 max 1，故把零项纳入 sup 与纸面剔除零项得到同一个 N。

PolynomialBounds 的正负界要求 x≥B，并保证严格符号；正性用 x≥1 且 x>S/|c_K|，负性通过取负保留 B。MainReduction 两个 residue_model 引理实际都以 uniformResidueBound 为 N。正性分支证明全部 j,r 的正领先系数；负性只需要异常余数的负领先系数，但仍可用全部 j,r 的同一最大界。因此 statement.md 用原纸面 F 生成的具体 N 被覆盖。两个 TargetStatements Prop 本身只写存在 N；本次确认显式公式另外检查了这些证明连接，不能仅凭 Prop 的表面类型声称覆盖有效界。

## 5. 奇数临界与无条件闭合（S4，已消解）

j<d、非临界偶数、非临界奇数、超阈值负性均连接到实际 concreteResiduePolynomial。异常条件始终是 m∣r+2d。

临界 d≥2 且 Odd d 推出 d≥3。CriticalReduction 证明异常分支2d次系数为零；CriticalCancellations 还证明平移后2d−1次系数为零，并给次数≤2d−2。MainClassification 的 critical_centered_second_formula 把实际2d−2次系数识别为 betaExpressionQ，再由 critical_beta_q_positive 得严格正性。这里没有把一个未识别的形式 beta 的正性当作实际系数的证明。次数界加非零系数识别 leadingCoeff；平移保持领先系数后返回原 residueTransform。criticalCenterShift=d+(2d+m)/2 正是先 t=n+d 再作纸面中心平移的总位移。

main_classification_proved 没有额外 hcritical 等前提，above_threshold_failure_proved 同样无外加假设。旧归约定理注释里的 remaining obligation 不代表最终入口仍有该假设。d=1明确不在域中，未将其非严格边界扩展为严格分类。

## 6. 结论与限制

完整检查 statement.md 的两个无限结论、有效界及范围限制，未发现未消解的陈述差异。checked_entire_claim=true，open_issues为空。上述发现记录参数类型编码、Bernoulli与递推构造、常数规范、零多项式界和旧入口身份的实际差异及其解决理由。

未重跑 Lean 构建、公理检查或 leanchecker，未做形式化执行记录审计，未重新证明全部系数引理，未联网查新或核验外部文献。PASS只限陈述对应性，不替代 formal_audit，也不单独构成公开授权。未修改作者证明或材料，写入仅限本独立响应目录。
