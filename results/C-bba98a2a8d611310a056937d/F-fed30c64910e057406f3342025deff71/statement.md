# QP01 精确主命题（来源候选；待本主库验证）

参数 d,m 为整数且 d≥2、m≥2，n 为非负整数。定义
p(d,m;n)=[z^n]((1-z)^(-2d)(1-z^m)^(-1))
=Σ_{v=0}^{⌊n/m⌋} binom(n-mv+2d-1,2d-1)。
对任意序列 f 与正整数 j，定义
T_j(f)(n)=Σ_{k=0}^{2j} (-1)^(k+j) binom(2j,k) f(n+k) f(n+2j-k)。
令 C_d=binom(2d,d)，M_d=1+C_d/2（整数）。

主命题：
[∃ N∈ℕ，∀ n∈ℕ，n≥N ⇒ ∀ j∈ℕ，1≤j≤d ⇒ T_j(p(d,m;·))(n)>0]
当且仅当 [d 为偶数，或 (d 为奇数且 m≤M_d)]。
奇数 d 且 m>M_d 时，存在 N，使所有 n≥N 且 m | (n+2d) 均有 T_d(p)(n)<0。

有效界采用来源证明第3、4节的有理剩余类多项式：p 在每个模 m 剩余类上的精确多项式为 F_r(X)=P(X)+b_r；P、b 依来源证明(4.4)、(4.5)给出的有限有理公式定义。令
h_(j,r)(X)=Σ_{k=0}^{2j}(-1)^(k+j)binom(2j,k) F_((r+k) mod m)(X+k) F_((r+2j-k) mod m)(X+2j-k)。
对非零 h(X)=Σ_{i=0}^K c_i X^i（c_K≠0），B(h)=1+ceil(Σ_{i<K}|c_i|/|c_K|)。
正性情形可取 N=max({1}∪{B(h_(j,r)):1≤j≤d,0≤r<m,h_(j,r)≠0})；负性情形使用同一有限非零多项式界。
这里的系数识别与该界的适用性仍须验证；不是以定义代替其证明。

范围限制：仅上述指定族；不解决 Gajdzica 2024 Problem 5.6 的所有拟多项式或任意分拆族。d=1 不纳入严格正性分类。周期边界通式等作为支持材料，不另冒称已固定引理。

来源：proofs/qp_laguerre_draft.md 第1、3、4、5、6节；paper/main.tex；REPORT.md。数学出处是 Gajdzica, Research in Number Theory 10 (2024), article 46, DOI 10.1007/s40993-024-00532-7，特别是 Theorems 4.3–4.4、Examples 4.5–4.6、Problem 5.6。此处仅转录来源定位，本轮未联网核实。
