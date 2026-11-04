# QP01 查新增量复核（研究甲，2026-10-29）

项目 P-e0470a3e0dd8f6277bfad9a0；命题 C-bba98a2a8d611310a056937d revision 1；尝试 A-886620b7af8e1a5127275dd8；父包 PKG-26e91aeda5851f6f64892705。本报告是本工作会话的查新记录，不是全新上下文的独立审查。

## 判断及检索卡

状态采用 `partial_known`：已核实相关充分条件和已知特例；本轮所读来源中没有确认本族的完整二参数分类，但访问覆盖仍有缺口，不能确认全球首次，也不能将未检出等价结果等同于排他证明。主分类、周期边界公式、奇数临界分支分别保留有限检索结论。

对象为生成函数 (1-z)^(-2d)(1-z^m)^(-1)，d,m≥2，固定参数后 n→∞，同时考虑 1≤j≤d 的离散 Laguerre 严格正性。比较的三个目标：A 全参数必要充分分类及超过奇数阈值的负剩余类；B 精确拟多项式的首个周期边界系数；C 奇数临界等号时的消去与下一非零系数。d=1、不指定误差模的 little-o 序列、任意分拆多重集和迭代 r-log-concavity 都不能自动并入。

检索词实际包括：`Gajdzica Laguerre quasi-polynomial partitions periodic coefficients solution 2025 2026`；`"Gajdzica" "Laguerre" "5.6"`；`"periodic boundary coefficient" Laguerre`；`"odd" "threshold" "Laguerre inequalities" partitions`；`"discrete Laguerre" "periodic" partition`；`"Laguerre" "central binomial" partitions`；`"restricted partitions" "Laguerre" classification`；以及 proof / solved / solution / formalization / Lean、quasipolynomial 拼写变体。仅发送公开人名、题名、领域词，没有上传本项目证明。

## 五类渠道与证据

| 渠道 | 本轮实际动作 | 覆盖结果与限制 |
|---|---|---|
| 学术索引、前向引用 | 开放搜索原题、作者、关键词和近年结果；重新读取期刊正文；尝试 OpenAlex W4394985659 引用 API、Semantic Scholar 引用 API、zbMATH | 原论文可访问；API 在 web 工具返回不可访问，不能把失败记为零引用；MathSciNet 未授权、未访问。旧报告的空列表不冒充本轮空列表 |
| 预印本、作者材料 | 读取 arXiv 2310.13814v1、2305.00085v1、2509.11246v1、2607.11568v1；作者机构发表表至2026年 | 更正了两个无效 v2 URL，v1 正文可访问；arXiv API 失败。没有读取所有新文、所有作者材料或订阅最终版本 |
| 数学社区、原题 | 原论文 Problem 5.6；MO、Math.SE 定向搜索；筛除正交多项式、Laguerre 函数等异题 | 未找到对应全参数解答；搜索结果并非论坛全库。未把无对应 Erdős 编号当成问题不存在 |
| GitHub 等开源社区 | 开放仓库/问题检索；重读 formal-conjectures 的 ErdosProblems/3.lean；沿其链接读取 openai/math 固定提交的 Conclusions.lean；读 RealRooted Issue #601 正文及后续更新；尝试 Issues/PR/Discussions 页面 | 实际源码与讨论已读；见下方精确排除。原生代码搜索及多个讨论入口失败；不能声称全 GitHub、全部无名定理或私有任务覆盖 |
| 本地成果索引 | rg 查询 RESULTS_INDEX.md、PROJECT_STATUS.md、PROJECT_STATUS_BY_SOURCE.md、agents 与 coordination 的 QP01/Laguerre/Gajdzica/命题ID | 命中本来源同一QP01包及派单，没有索引到另一个同题独立成果。UNI、LC为不同命题；未扩展研究。仅为本地索引去重，未语义遍历全部历史证明 |

实际 web 工具返回保存于 `evidence/qp01-verification/web*-results.json` 及 `web1-search-results.json`、`web3-search-results.json`、`web4-search-results.json`；其中失败文本是工具实际返回，不能推断为远端 HTTP 状态。旧来源报告和缺失快照仅作历史记录复用，不能代替本次访问。机器原始抓取如另有成功，详见同目录 sources/manifest.json；不存在的记录不得推定已执行。

## 精确命题对照

| 来源及原文定位 | 对方假设、结论 | 与 A / B / C 的关系 |
|---|---|---|
| [Gajdzica 2024](https://link.springer.com/article/10.1007/s40993-024-00532-7)，§4 Thm 4.3–4.4、Ex 4.5–4.6、§5 Problem 5.6 | 最高到临界次数系数恒定的充分条件；分拆族有子多重集 gcd 条件；另有周期例子和四个1加300特例 | 平滑首项及该特例已知。对本族 k=2d+1，Thm4.4 的单元素子集条件因 {m} 失败。A/B/C 的一般结论未在这些条款出现。原题更广，不能声称完全解决它 |
| [2310.13814v1](https://arxiv.org/html/2310.13814v1)，§4–5 | 原期刊论文的预印本，非独立先行解答 | 不重复计为第二个发现；核对公式与问题身份 |
| [2305.00085v1](https://arxiv.org/html/2305.00085v1)，Thm4.8–4.10及证明 | 讨论反复作用对数凹算子后的 r-log-concavity | 与一次高阶 T_d 不同，不能用其必要条件直接否定或证明 A/B/C。旧材料的纠错线不纳入原创主张。Acta2025最终全文仍未取得 |
| [2509.11246v1](https://arxiv.org/html/2509.11246v1)，Def1、Thm2.1–2.5、§4–5 | 固定 n，权函数参数 ell 充分大，研究一次 log-concavity 的符号分布 | 极限参数、生成函数和阶数均不同；不提供 A 的固定(d,m)、n充分大分类，也未给出本 B/C |
| [2607.11568v1](https://arxiv.org/html/2607.11568v1)，Thm1.1–1.2及§3–5 | 归一化算术函数递推多项式的次乘性，条件与 x、算术函数界有关 | 所得不等式不是 T_d，不能作为本族高阶分类的先行解答 |
| [Roy 2026](https://link.springer.com/article/10.1007/s00026-026-00847-5)，Thm1.1 | 已有最终对数凹性加初值条件推出乘法不等式 | 不是证明本族 T_d 的全部阶必要充分条件；未见 B/C。发布日期2026-09-29，避免只按旧文献列表判断 |

周期边界项 B 是精确分支多项式的系数恒等式：平滑项之外有移位的循环差分贡献，不能把“存在周期例子”当成该通式已证，也不能把平滑项重新归于本项目。C 必须同时比较两次消去、实际次数下降与正系数识别；单有一个正表达式或有限实验不等于完成 C 的形式化。上述比较属于本次阅读判断，不是独立证明认证。

原论文 Ex4.6 写有 `n not congruent 297 mod 300` 的等号条件，而项目(4.8)的特殊类是 `m | n+2d`，d=2 时为296。T_2 的求和形式等于该例 h_A 的两倍，所以归一化倍数不能解释一位偏移。该差异交由正式陈述审查处理；本报告不修改原文、不主张纠错优先权。若有限对照证书存在，见 finite-alignment-checks.json，其有限性质不替代一般证明。

## 开源线索的语义核对

1. [formal-conjectures/FormalConjectures/ErdosProblems/3.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/3.lean) 的 quasipolynomial 命中是等差数列密度界文献；其 `Erdos3.erdos_3` 是倒数和发散集合包含任意长等差数列，目录内证明为 sorry 并链接外部文件，不是 QP01。
2. 已沿链接实际读到 [openai/math，提交 adc7f1241b42e322a6451854ab7e4b4c146bf78a，Conclusions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean)。`manuscript_main_theorems` 以已有相对提升引理组合密度与等差数列结论；读了本文件的证明体，未运行其依赖证明。它不涉及分拆系数或 Laguerre 变换，不能当作本题已解/未解的全库证据。
3. [PerAlexandersson/RealRooted Issue #601](https://github.com/PerAlexandersson/RealRooted/issues/601) 实际研究含导数的多项式递推、Weyl算子和实根/交错，使用指数型生成函数的集合分拆模型。其 Laguerre boundary 不是本题周期剩余类边界。页面可读；链接的 sqrt-of-2 PR #558 返回404，提交74f3614入口未取到，明确不声称已复验其证明。
4. [openai/math CONTENTS](https://github.com/openai/math/blob/main/CONTENTS.md) 当前显示721稿件、373结果族，Laguerre/Gajdzica查找无命中。这只是索引筛查；其他仓库入口与失败查询不能把它升级成全库语义排除。

作者[机构发表表](https://apacz.matinf.uj.edu.pl/users/2196-krystian-gajdzica)已重读。订阅全文、完整前向引用、原生代码搜索和不可达讨论仍为开放缺口。下一轮优先处理这些缺口，若新发现相关声称解答，先取得精确证明再改变新颖性状态。

本轮已执行finite-alignment-checks.json中的5个精确有限对照：d=2,m=300的296/297类所得最高系数分别为151/540000和1/540000；d=3,m=11、r=5的插值次数4，最高系数5/44；m=12、r=6最高系数-1/51840。它们只核对列出的有限点，未把插值次数上界或具体分支表示当作已完成的Lean证明。
