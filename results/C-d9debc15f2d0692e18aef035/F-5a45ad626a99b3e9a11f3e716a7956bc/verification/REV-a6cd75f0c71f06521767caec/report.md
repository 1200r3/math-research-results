# Tatami：许可版本的独立反例与边界复审

**PASS**。本次由原反例审稿人继续同一独立上下文，复用原全范围验证，并把结论绑定到下列新包。没有另行登记一个审稿人或新上下文，也未重新执行原有限检查。

| 绑定 | 原完整检查 | 许可版本复审 |
|---|---|---|
| 审查请求 | REQ-5c06c37f07aaa5996b64cd0a | REQ-010b2ee2142df959a05b9769 |
| 成果包 | PKG-8e587cb4625e66fe71a84c97 | PKG-01b66dea6d410d13175a741e |
| 包 manifest SHA-256 | 43b98be16112d6f056234dc2fc5b3db7f5bdc5f012c48116f903083554a2a38f | 57c316b18a6460d8ad59d4dfb38d11d33b66fc9cf561315325da8c1d569131d9 |

命题 C-d9debc15f2d0692e18aef035 rev. 1，声明 SHA-256 为 `e8afb37a5d297a241ad6881e1bf18d7d7a175caad95c41cfe4863b284910c7c7`。审查类型、审稿人、模型及上下文均未改变（counterexample_search / independent-sol-boundary / gpt-6.1-sol / CTX-5522a3a0959e8826718f2b1a）。

原审查 T-B1 至 T-B3 覆盖全部奇偶分支、区块公式的范围与两处排印问题、角分配、末例外和最小截点，并独立逐格计数 27 个小矩形。 详见[原完整报告](../../responses/boundary-tatami/report.md)及[原独立检查日志](../../responses/boundary-tatami/independent-check.log)。原绑定响应、原报告与原独立日志的 SHA-256 依次为 `20e19428127008655250d3779d94e745bfa8140a0a99a670c63af9657584e5fe`、`75b0ff2ecc9202175a10c7064fcbc74a03614cdb4026c81e6109dfc4bdfb8830`、`d0bcb0d1ded14118264e71ac4b464de9ceab4a819b52396d33967aa348734e3d`。

**T-BD｜差量核查（2026-11-06T02:45:35+00:00）。** 两请求只改动创建时间、请求 ID、成果包 ID 和包 manifest SHA-256。两个请求的材料清单、命题修订、声明哈希、来源及执行记录字段一致，审查说明与查新说明也逐字节一致。独立列出两个实际材料目录，排除遗漏与额外文件，再分别读取并重算每份文件的字节数及 SHA-256，并直接比较原/新文件字节。结果：

| 附送材料 | 字节数 | 原、新实际 SHA-256（相同） |
|---|---:|---|
| `code/check_coefficients.py` | 1082 | `ef55c277ad20fd95acdcf383f6e083cb6a092ddc9a269b2391970ff6bd5e4883` |
| `evidence/finite-arithmetic.log` | 1263 | `2750ef5cb1f0083692d63deaa556d2463cbb749447dc3ec5ad5747b33ed887ed` |
| `proofs/main.tex` | 5583 | `712e26c6f8dbbf6a25454bc7a0903a819cb79bb4487c48c7a748e650c8828505` |
| `proofs/one-monomino-stabilization.md` | 3502 | `6d486d88bc1460521dd1310f9366f829f8213a178b11ca67423df78203d9e72c` |
| `proofs/tatami-one-monomino.pdf` | 185790 | `3bd6e06be92849c58b62f417622d543d5fb0db4cb369ea161c60d9de60c155df` |
| `statement.md` | 1061 | `e8afb37a5d297a241ad6881e1bf18d7d7a175caad95c41cfe4863b284910c7c7` |

所有附送的数学材料、程序与实跑证据均与原审查对象逐字节一致，因而原全范围反例与边界检查适用于此次新绑定。差量检查不评价已选择的正文和代码许可条款，也不涵盖请求材料以外的包元数据。未发现反例或未解决问题。
