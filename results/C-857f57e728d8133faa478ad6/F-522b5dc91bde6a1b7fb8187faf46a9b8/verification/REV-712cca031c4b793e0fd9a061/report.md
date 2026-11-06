# Rado3：许可版本的独立反例与边界复审

**PASS**。本次由原反例审稿人继续同一独立上下文，复用原全范围验证，并把结论绑定到下列新包。没有另行登记一个审稿人或新上下文，也未重新执行原有限检查。

| 绑定 | 原完整检查 | 许可版本复审 |
|---|---|---|
| 审查请求 | REQ-1d54ae13148c5675a319edbd | REQ-0f4325117062adbabd72b6c5 |
| 成果包 | PKG-557bf624780f746a56e17478 | PKG-ba7ec3c8258d02885b54aae9 |
| 包 manifest SHA-256 | 7748c2c8340e9bbfc01ff01f922005015f4cd31eadad9b6db1da318d9ad7a1b6 | 182de2ad44dd39be45360d5e8a58b0c7f0845aa4c54184b06d06d2e50a7e5f92 |

命题 C-857f57e728d8133faa478ad6 rev. 2，声明 SHA-256 为 `4023f1270cb923cc808c7a52ee9aad94a75788354d2468aa456d34cb455e6fc4`。审查类型、审稿人、模型及上下文均未改变（counterexample_search / independent-sol-boundary / gpt-6.1-sol / CTX-4cf71702202f56f0f4c579d8）。

原审查 R-B1 至 R-B3 覆盖全部移位分支：非对角的二进估值、周期、零移位、空色与重复输入；对角的进位和精确端点。独立检查含 504 个小移位三元组、各周期和高估值边界，以及 c=0,1,2 的临界两个区间。 详见[原完整报告](../../responses/boundary-rado/report.md)及[原独立检查日志](../../responses/boundary-rado/independent-check.log)。原绑定响应、原报告与原独立日志的 SHA-256 依次为 `9c89079dab217c32d3a68300784c878850e617f14958fa3030f6302d8da731dc`、`94a1e3ee6d3e8ab47d6a3d7cf67c31994571f1fd0ba8119e6aa96358439248ba`、`7a2a6fb1b3a27f94396f778428ede94a41352c3e6bea66380e213a09366ba3ff`。

**R-BD｜差量核查（2026-11-06T02:45:35+00:00）。** 两请求只改动创建时间、请求 ID、成果包 ID 和包 manifest SHA-256。两个请求的材料清单、命题修订、声明哈希、来源及执行记录字段一致，审查说明与查新说明也逐字节一致。独立列出两个实际材料目录，排除遗漏与额外文件，再分别读取并重算每份文件的字节数及 SHA-256，并直接比较原/新文件字节。结果：

| 附送材料 | 字节数 | 原、新实际 SHA-256（相同） |
|---|---:|---|
| `code/check_finite_arithmetic.py` | 1957 | `2e7e1422a3faecfa1f7cd8900ba458ed8bc8afdadd58f19f9da5533ae8f8ad6f` |
| `evidence/finite-arithmetic.log` | 927 | `6232c319d16f0f5eadb6221edc8bfd897e38ec31c29b89a445e4506744f6bc43` |
| `proofs/main-theorem-U.md` | 3060 | `e037498b1f7dbfd0afa43d731c6f22af8a5a57365f92b377a8103f42d50f7ee7` |
| `proofs/main.tex` | 5123 | `013fc6a6316ad4350432079103caeedfc028020a30bf8147fc0cd65a5ffc0fe3` |
| `proofs/rado3-shift-classification.pdf` | 194200 | `41a8611da8542830e63bb047902c9ba6d9cd42ff073736775a4b804348f896e3` |
| `statement.md` | 787 | `4023f1270cb923cc808c7a52ee9aad94a75788354d2468aa456d34cb455e6fc4` |

所有附送的数学材料、程序与实跑证据均与原审查对象逐字节一致，因而原全范围反例与边界检查适用于此次新绑定。差量检查不评价已选择的正文和代码许可条款，也不涵盖请求材料以外的包元数据。未发现反例或未解决问题。
