# Reproduction

Delivery audit, 2026-11-01: all five source entry points and the original evidence are byte-identical to the reviewed r5 snapshot. The five most recent complete successful run records and their log hashes were checked again; no mathematical computation was rerun for this documentation-only delivery. See ../evidence/delivery-audit-20261101.json. The single proof change clarifies the existing normalization convention and does not change any numerical input or expected output.

The absolute paths below document the original machine. When transferring to an interpreter on D: or another device, use its actual Python path and the new checkout path; do not execute these output-writing programs inside an immutable package. The historical environment was Python 3.14.7. No third-party numerical library is required, so this delivery required no new download.

Use the workspace's trusted Python 3.14.7 at C:/msys64/mingw64/bin/python.exe. All five programs use only the standard library (Fraction, Decimal, random, json, pathlib, math). No installation, download, external code, or GPU is required. Mathflow is version 2.0.0. The original computations used Decimal precision 80 and deterministic seed 20261025.

Read the five code/check_*.py entry points before execution. check_defect.py constructs exact rational models, harmonic gauges and resolvent coefficients, selects the positive Perron branch, checks the optimized nonlinear energy, and compares exact cubic reductions. check_hierarchy.py checks the sharp twelfth-order example. check_arbitrary_order.py checks the original moment construction for m=1,...,6. check_dimension.py checks the smaller construction for m=1,...,8 and a minimal three-vertex quartic example. check_zero_diagonal.py checks the four-cycle and K_(2,3) examples in exact weighted coordinates, with Decimal radical matrices as numerical confirmation. All are author checks.

From the toolkit directory, with an active authorized session for the attempt, run these PowerShell commands. Use new log names on each reproduction; output JSON is regenerated, so preserve earlier evidence if changes are being tested.

```powershell
$mathPython = 'C:\msys64\mingw64\bin\python.exe'
$mathDevice = 'C:\Users\Administrator\Desktop\数学\codex-workspace\device'
$mathWork = 'C:\Users\Administrator\Desktop\数学\codex-workspace\projects\perron-cycle-defect\attempts\A-4e1d1a2aa13cc2d57162c2d5\work'
& $mathPython workflow.py device-status --device $mathDevice
& $mathPython workflow.py run-job --device $mathDevice --cwd $mathWork --threads 1 --memory-gb 0.25 --seconds 120 --log ($mathWork + '\evidence\reproduction-defect-01.log') -- $mathPython -B code/check_defect.py
& $mathPython workflow.py run-job --device $mathDevice --cwd $mathWork --threads 1 --memory-gb 0.25 --seconds 60 --log ($mathWork + '\evidence\reproduction-hierarchy-01.log') -- $mathPython -B code/check_hierarchy.py
& $mathPython workflow.py run-job --device $mathDevice --cwd $mathWork --threads 1 --memory-gb 0.25 --seconds 120 --log ($mathWork + '\evidence\reproduction-arbitrary-order-01.log') -- $mathPython -B code/check_arbitrary_order.py
& $mathPython workflow.py run-job --device $mathDevice --cwd $mathWork --threads 1 --memory-gb 0.25 --seconds 120 --log ($mathWork + '\evidence\reproduction-dimension-01.log') -- $mathPython -B code/check_dimension.py
& $mathPython workflow.py run-job --device $mathDevice --cwd $mathWork --threads 1 --memory-gb 0.25 --seconds 120 --log ($mathWork + '\evidence\reproduction-zero-diagonal-01.log') -- $mathPython -B code/check_zero_diagonal.py
```

Expected results: returncode 0, timed_out false, status passed in all generated JSON files. The first reports 18 finite graphs and 90 parameter points. The next two retain the r3 checks. The dimension program reports orders 4 through 32, dimensions 4,6,8,10,12,14,16,18, and quartic coefficient 2/16875 on three vertices. The zero-diagonal program reports quartic coefficient 36/300125 on four vertices and eighth-order coefficient 5/512 on five vertices. Scaled defects converge at the next even power as the parameter is halved. The minimum-dimension lower bounds are proved in the text, not by numerical enumeration.

Original runs:

| Log | Job | Result |
|---|---|---|
| numerical-run-01.log | JOB-e871903c1d75721c898ae72f | failed, exit 1, not timed out; Newton found a nonpositive eigenvector |
| numerical-run-02.log | JOB-20ae1f373f6d9f0c7b38fe30 | passed, exit 0, not timed out; positive branch initialization added |
| hierarchy-run-01.log | JOB-816d641f8d348449e43feddf | passed, exit 0, not timed out |
| arbitrary-order-run-01.log | JOB-f1ccf808cd47a733a2d00d3b | passed before bipartite-lift checks were added; historical subset |
| arbitrary-order-run-02.log | JOB-deca61286c45d64ea3cd1795 | passed, exit 0, not timed out; includes bipartite lift |
| dimension-run-01.log | JOB-986377738536d0740cf83dbf | passed, exit 0, not timed out; new T7-T8 checks |
| zero-diagonal-run-01.log | JOB-ee01549711b3a339b0cda379 | passed, exit 0, not timed out; new T9 checks |

The failed source is retained as research/check_defect_v1_failed_newton.py. It is not a recommended reproduction entry point. The .log.result.json files record the actual job ID, exit status, ending time, and log hash; evidence/job-history records preserve the device's interpreter label, resource reservation, and release information. The launch commands are transcribed from the actual tool calls in evidence/commands.json, not recovered from the device history. Decimal residual widths are numerical residuals, not directed-rounding interval certificates. The universal proof is the written argument; finite numerical success cannot substitute for it.

Pack/validate checks only the package contract and hashes. They do not run these scripts or certify the mathematics.
