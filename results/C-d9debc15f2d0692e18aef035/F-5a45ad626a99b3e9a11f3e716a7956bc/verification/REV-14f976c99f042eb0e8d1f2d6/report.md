# 独立纸面审查 A：单方块榻榻米近方形稳定性（许可版差异复核）

**PASS。** 原完整纸面审查的结论适用于此次封存版本，完整命题已检查，无未关闭问题。此为同一独立审稿人的复核，不另计审稿人或上下文。

命题 C-d9debc15f2d0692e18aef035 第 1 版。审稿人 independent-sol-paper-a，模型 gpt-6.1-sol，上下文 CTX-067f7871baee939e1b5b14d1。

| 版本 | 成果包 | 请求 | 清单 SHA-256 |
| --- | --- | --- | --- |
| 原封存 | PKG-8e587cb4625e66fe71a84c97 | REQ-5ec2ba2109495e593535ffb3 | 43b98be16112d6f056234dc2fc5b3db7f5bdc5f012c48116f903083554a2a38f |
| 许可版 | PKG-01b66dea6d410d13175a741e | REQ-23540966d55b4470d14c84d4 | 57c316b18a6460d8ad59d4dfb38d11d33b66fc9cf561315325da8c1d569131d9 |

[原完整纸面报告](/E:/数学总目录/reports/Rado3-Tatami-20261106/responses/paper-a-tatami/report.md) 的 SHA-256 为 ab1fc662bbd137f6c144e025daebf05e3c7717c558a64d90519cc91f75abb2cf；原回执 SHA-256 为 b6a549cd51916d9e3869c736ee3680f3742477e9b8b38fe7d8c2982f3ec4a9c4。原报告 A-T1 至 A-T4 覆盖完整奇偶与标号定义、已发表拼块分解的两处排印修正、所有目标宽度的贡献、四角分布、两个最小阈值及独立小例。原报告中关于明确 r≥K 的表述建议仍为非阻碍性建议。

逐字段比较两份请求：仅 created、request_id、package_id 和 manifest_sha256 变化；两份模板仅 request_id 和 manifest_sha256 变化。命题 ID、版本、陈述哈希、来源、审稿标识、上下文和材料清单保持一致。

独立枚举两边的 materials 目录，均恰有下面 6 个文件。对每一对实际文件分别计算 SHA-256、字节数，并直接比对完整字节。结果全部相同，且与各自请求清单相符。

| 材料路径 | 字节数 | 两边实际 SHA-256 |
| --- | ---: | --- |
| code/check_coefficients.py | 1082 | ef55c277ad20fd95acdcf383f6e083cb6a092ddc9a269b2391970ff6bd5e4883 |
| evidence/finite-arithmetic.log | 1263 | 2750ef5cb1f0083692d63deaa556d2463cbb749447dc3ec5ad5747b33ed887ed |
| proofs/main.tex | 5583 | 712e26c6f8dbbf6a25454bc7a0903a819cb79bb4487c48c7a748e650c8828505 |
| proofs/one-monomino-stabilization.md | 3502 | 6d486d88bc1460521dd1310f9366f829f8213a178b11ca67423df78203d9e72c |
| proofs/tatami-one-monomino.pdf | 185790 | 3bd6e06be92849c58b62f417622d543d5fb0db4cb369ea161c60d9de60c155df |
| statement.md | 1061 | e8afb37a5d297a241ad6881e1bf18d7d7a175caad95c41cfe4863b284910c7c7 |

因此陈述、证明正文、TeX、PDF、补充代码及证据日志均无变化；原审查范围与结论完整保留。此次差异复核限于送审请求和材料，不重新执行代码或审定发布许可。原审查和封存文件均未改动。
