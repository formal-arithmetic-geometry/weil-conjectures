# F66Adj MDA validation

Root 6122: 3,897,905 calls; 45,914.132 ms comparison-exclusive; labels {'M0': 1, 'M1': 2961163, 'M2': 9, 'Matched': 936732}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 6122:1 | 0 | unattributed/fallback | `Eq` / `Eq`; Expr in JSONL | `unknown` | 2,961,163 | 45,914.132 | trace; nested rows overlap |
| 6122:60 | 1 | application/argument[1] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 2,961,059 | 45,841.213 | trace; nested rows overlap |
| 6122:61 | 60 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 2,961,058 | 45,373.821 | trace; nested rows overlap |
| 6122:62 | 61 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 2,961,057 | 44,945.368 | trace; nested rows overlap |
| 6122:68 | 62 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 2,961,052 | 44,504.093 | trace; nested rows overlap |
| 6122:69 | 68 | lazy_delta/argument[7] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 2,961,004 | 44,330.332 | trace; nested rows overlap |
| 6122:70 | 69 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 2,961,003 | 44,218.500 | trace; nested rows overlap |
| 6122:71 | 70 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 2,961,002 | 44,156.043 | trace; nested rows overlap |
| 6122:72 | 71 | second_whnf/whnf-iota-exposure | `Equiv.invFun` / `Equiv.invFun`; Expr in JSONL | `unknown` | 2,961,001 | 44,113.701 | trace; nested rows overlap |
| 6122:461404 | 72 | application/argument[0] | `CategoryTheory.NatTrans.app` / `CategoryTheory.NatTrans.app`; Expr in JSONL | `unknown` | 2,610,465 | 36,113.998 | trace; nested rows overlap |
| 6122:461405 | 461404 | second_whnf/whnf-iota-exposure | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 2,610,464 | 36,010.774 | trace; nested rows overlap |
| 6122:461406 | 461405 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 2,610,463 | 35,261.330 | trace; nested rows overlap |
| 6122:461407 | 461406 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 2,610,462 | 34,567.470 | trace; nested rows overlap |
| 6122:461492 | 461407 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 2,610,388 | 33,917.207 | trace; nested rows overlap |
| 6122:461493 | 461492 | lazy_delta/argument[7] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 2,610,346 | 33,646.127 | trace; nested rows overlap |
| 6122:461494 | 461493 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 2,610,345 | 33,450.419 | trace; nested rows overlap |
| 6122:461495 | 461494 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 2,610,344 | 33,311.040 | trace; nested rows overlap |
| 6122:461496 | 461495 | second_whnf/whnf-iota-exposure | `Equiv.invFun` / `Equiv.invFun`; Expr in JSONL | `unknown` | 2,610,343 | 33,200.229 | trace; nested rows overlap |
| 6122:461527 | 461496 | application/argument[0] | `CategoryTheory.NatTrans.app` / `CategoryTheory.NatTrans.app`; Expr in JSONL | `unknown` | 2,610,314 | 33,134.635 | trace; nested rows overlap |
| 6122:461528 | 461527 | second_whnf/whnf-iota-exposure | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 2,610,313 | 33,059.740 | trace; nested rows overlap |
| 6122:461529 | 461528 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 2,610,312 | 32,379.049 | trace; nested rows overlap |
| 6122:461530 | 461529 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 2,610,311 | 31,759.055 | trace; nested rows overlap |
| 6122:461536 | 461530 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 2,610,306 | 31,200.495 | trace; nested rows overlap |
| 6122:461537 | 461536 | lazy_delta/argument[7] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 2,609,852 | 31,017.476 | trace; nested rows overlap |
| 6122:461538 | 461537 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 2,609,851 | 30,907.099 | trace; nested rows overlap |
| 6122:461539 | 461538 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 2,609,850 | 30,842.201 | trace; nested rows overlap |
| 6122:461540 | 461539 | second_whnf/whnf-iota-exposure | `Equiv.invFun` / `Equiv.invFun`; Expr in JSONL | `unknown` | 2,609,849 | 30,796.349 | trace; nested rows overlap |
| 6122:461570 | 461540 | application/argument[0] | `CategoryTheory.NatTrans.app` / `CategoryTheory.NatTrans.app`; Expr in JSONL | `unknown` | 2,609,821 | 30,787.326 | trace; nested rows overlap |
| 6122:461571 | 461570 | second_whnf/whnf-iota-exposure | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 2,609,820 | 30,688.010 | trace; nested rows overlap |
| 6122:461572 | 461571 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 2,609,819 | 29,529.573 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | Direct calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 310,390 | 15,642.337 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 761,198 | 11,194.275 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 438,420 | 3,895.205 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 719,539 | 2,893.311 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 719,539 | 2,079.279 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 176,569 | 1,668.135 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 73,771 | 1,331.771 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[2] | gateway/component candidate | aggregate | quick | 46,537 | 963.830 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[4] | gateway/component candidate | aggregate | application | 45,797 | 919.923 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | lazy_delta | 8,709 | 695.899 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[1] | gateway/component candidate | aggregate | quick | 16,187 | 656.247 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[3] | gateway/component candidate | aggregate | quick | 26,505 | 523.125 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | application | 15,466 | 438.595 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[11] | gateway/component candidate | aggregate | application | 11,229 | 433.130 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | lazy_delta | 24,338 | 383.871 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[5] | gateway/component candidate | aggregate | application | 26,926 | 305.648 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[3] | gateway/component candidate | aggregate | application | 49,823 | 291.649 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[12] | gateway/component candidate | aggregate | application | 11,227 | 240.709 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | application | 15,487 | 225.784 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[8] | gateway/component candidate | aggregate | application | 11,640 | 193.936 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[20] | gateway/component candidate | aggregate | lazy_delta | 7,638 | 99.614 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[19] | gateway/component candidate | aggregate | lazy_delta | 7,640 | 96.085 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | lazy_delta | 11,516 | 89.745 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[10] | gateway/component candidate | aggregate | application | 11,229 | 86.313 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[9] | gateway/component candidate | aggregate | lazy_delta | 8,598 | 72.640 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[9] | gateway/component candidate | aggregate | application | 11,229 | 66.766 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[4] | gateway/component candidate | aggregate | quick | 78 | 51.154 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / binder-domain[2] | gateway/component candidate | aggregate | quick | 26,494 | 42.487 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[12] | gateway/component candidate | aggregate | lazy_delta | 7,726 | 41.970 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / fallback | gateway/component candidate | aggregate | unattributed | 1 | 33.339 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
