# QP01 两项Lean主证明的衔接说明

本文是研究甲给协调员的作者说明，不是独立审查。纸面候选结果来自用户指定来源包；本轮在原指定工作副本编写具体分拆表示及主命题的形式化连接。原十份Lean源码、两项Prop定义、命题文件与旧审稿保持原样。

## 精确目标

| 原目标 | 新的无条件证明 | 范围 |
|---|---|---|
| `PartitionLaguerre.mainClassification` | `PartitionLaguerre.main_classification_proved`，MainClassification.lean | 自然数d,m≥2；存在共同N，使全部自然数n≥N与1≤j≤d严格为正，当且仅当d偶数，或d奇数且m≤criticalIndex d |
| `PartitionLaguerre.aboveThresholdFailure` | `PartitionLaguerre.above_threshold_failure_proved`，ConcreteLeadingCoefficient.lean | d,m≥2，d奇数且超过阈值时，在m整除n+2d的所有充分大自然数点严格为负 |

`criticalIndex d=1+Nat.centralBinom d/2`；中央二项式的二整除性在临界主项消去中实际使用。d=1不在目标范围内。`AuditFinalQP01.lean`包含两个以原Prop为目标的`example`，并显式检查所有命名证明的类型和公理；不是只让Prop定义通过编译。

## 从原始有限和构造实际多项式

ConcretePartitionModel使用Bernoulli有限幂和与降阶Pochhammer多项式构造每个实际剩余类多项式F_r，并从原`partitionCount`有限和证明p(n)=F_(n mod m)(n)。重排中的自然数减法均在真实求和范围内证明合法。

PolynomialPart从共同的步长m反差分恒等式证明所有F_r只差常数，给出实际p=P+b。PolynomialPartDegree证明P与全部F_r的次数为q=2d，首项a=1/(m q!)。这里P选F_0，常数项可以不同于纸面复根主部的规范化；后续高次系数不受该常数选择影响。

本轮没有把p=P+b或F_r表示作为主定理的额外假设。MainReduction中原先带这些假设的连接定理仍保留，但两个最终无条件证明已经用具体构造填充全部前提。

## 平滑项与周期边界

PartitionRecurrence、PartitionDifference从Pascal恒等式和分拆有限和推出普通前向差分

`D^q p(n)=1_(m|n+q)`。

对P的q阶差分为1/m，因此PeriodicDifference证明实际周期项满足

`D^q b(n)=1_(m|n+q)-1/m`。

LaguerreMoments严格证明低于2j的加权中心矩为零、2j阶矩为(-1)^j(2j)!、所有奇数中心矩为零。SmoothMonomial与SmoothPolynomial用反转多项式和齐次性证明实际高次消去，平滑首项为a²(2j)!choose(q,j)。当j<d时其次数高于周期交叉项，故对每个剩余类为正。

在j=d时，ConcreteLeadingCoefficient识别实际q次系数为

`[centralBinom d+2(-1)^d(m*1_(m|r+2d)-1)]/(m²(2d)!)`。

这里r是原n的模m类，整除偏移n+2d在Lean中核对。只有该系数非零时才将它识别为实际首项。ConcretePositiveBranches解决全部非临界正性与必要性方向；超过奇数阈值时，实际特殊类首项为负，并由显式系数界得到原负性主命题。

## 奇数临界等号

令sigma=(q+m)/2，S(X)=P(X-sigma)。CenteredPolynomial由降阶Pochhammer的反射和非零周期多项式必为常数，证明S为偶多项式。PolynomialTopCoefficients、ShiftTopCoefficients、CenteredSecondCoefficient进一步比较精确中心差分，得到

`S.coeff(q-2)=-a*q*(q-1)*(q+m²)/24`。

临界周期矩没有假设b自身均值为零。令g=D^(q-2)b；它是非零阶周期差分，整周期均值为零。CyclicDifference证明二阶差分与均值确定周期向量。CyclicGreen和CriticalGreenIdentification给出其实际值

`g(n)=-(m²-1)/(12m)+t(m-t)/(2m)`，`t=(n+q-1) mod m`。

DifferenceProduct与CriticalPeriodicMoments据此证明在m整除n+q的类上B1=0，并在奇数d时得到

`B2=(m-1)/m*(-d²+d(2d-1)(m+1)/6)`。

NextLaguerreMoment用中心化降阶Pochhammer多项式与严格次数余项，计算下一偶数矩

`M_(2d+2)=(-1)^d(2d+2)!*d/12`。

CriticalCenteredTransform把原实际剩余类变换作X方向的平移，周期标签仍是原n的剩余类r，不将有理中心坐标重新取模。CriticalCancellations证明特殊临界类q次、q-1次项消去、次数至多q-2。CriticalSmoothMonomials、CriticalBinomialIdentities和CriticalSmoothCoefficient计算平滑下一项，连同两个真实周期交叉项，在MainClassification中得到实际q-2次系数等于`criticalBetaQ d`。

CriticalBetaRational证明该有理表达式嵌入实数后恰等于已有`criticalBeta d`。只有在完成上述实际系数识别后才调用`critical_beta`正性。奇数d≥2自动有d≥3，因此该系数严格为正，实际首项次数为q-2；随后关闭完整主分类。

## 有效界与表述范围

实际正、负尾界均由`uniformResidueBound m d (concreteResiduePolynomial d m)`构造。其各类分量是`1+Nat.ceil(lowerCoefficientMass/abs leadingCoeff)`，包含max 1和对j、r的有限上确界。PolynomialBounds证明该界在有理数上有效，实际输入n为自然数，因此足以完成两项主命题。这里没有以“某个多项式最终有符号”的未定常数替代有效界。

Lean的F_r采用上述Bernoulli有限求和构造，没有逐字形式化纸面(4.4)的u_h递推、复根部分分式或形式留数表达式。已经严格证明的是同一原始分拆序列的精确剩余类模型与由它给出的有限显式界。此替代构造及其覆盖范围应由新的statement审查核对，不冒称纸面每一条展示公式都已逐字形式化。

一般实系数多项式的全部实数版本、任意ell的全部周期边界通式、未指定误差模的little-o推广、任意分拆族以及d=1严格分类均不在这两项已证明Prop的范围内。查新结论仍为partial_known、全球优先权unclear；Lean证明不消除文献访问缺口，也不构成全球首次证明。

## 证据与后续验收

最终验证的权威结果为evidence/qp01-verification/final-qp01-v1-result.json及外层run-job回执；未结束或失败的记录不作成功证据。此前真实超时、编译失败、缓存补齐和89+1公理补查均保留。最终全量审计包括43个证明模块、177条命名定理，以及两个原Prop的直接填充。

该研究包不自动改变主库formal验收状态。STANDARD要求主库保存检查记录，并由不同全新上下文分别进行完整statement核对和formal_audit；这些独立审查由协调员另外安排，旧审稿不自动变为本新证明包的审查。
