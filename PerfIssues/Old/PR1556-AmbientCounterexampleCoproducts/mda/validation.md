# PR1556 MDA validation

Root 6006: 6,670,198 calls; 184,293.573 ms comparison-exclusive; labels {'M0': 1, 'M1': 5006059, 'M2': 9121, 'Matched': 1655017}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 6006:1 | 0 | unattributed/fallback | `Eq` / `Eq`; Expr in JSONL | `unknown` | 5,006,059 | 184,293.573 | trace; nested rows overlap |
| 6006:4 | 1 | application/argument[1] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 5,006,058 | 184,244.532 | trace; nested rows overlap |
| 6006:5 | 4 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 5,006,058 | 183,846.985 | trace; nested rows overlap |
| 6006:6 | 5 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 5,006,058 | 183,468.124 | trace; nested rows overlap |
| 6006:12 | 6 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 5,006,053 | 183,093.823 | trace; nested rows overlap |
| 6006:13 | 12 | lazy_delta/argument[7] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 4,012,034 | 173,745.765 | trace; nested rows overlap |
| 6006:39 | 13 | application/argument[0] | `CategoryTheory.NatTrans.app` / `CategoryTheory.NatTrans.app`; Expr in JSONL | `unknown` | 4,012,022 | 173,647.956 | trace; nested rows overlap |
| 6006:40 | 39 | second_whnf/whnf-iota-exposure | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 4,012,021 | 173,449.528 | trace; nested rows overlap |
| 6006:41 | 40 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 4,012,020 | 172,282.291 | trace; nested rows overlap |
| 6006:42 | 41 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 4,012,019 | 171,175.052 | trace; nested rows overlap |
| 6006:60 | 42 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 4,012,008 | 170,076.988 | trace; nested rows overlap |
| 6006:61 | 60 | lazy_delta/argument[7] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 3,926,393 | 168,765.508 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 542,685 | 89,082.328 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 1,289,100 | 29,603.340 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 451,393 | 14,647.570 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 446,677 | 13,766.413 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | lazy_delta | 940 | 4,715.552 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 126,864 | 4,050.285 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 262,963 | 3,773.453 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 932,066 | 3,745.480 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | lazy_delta | 19,482 | 3,472.005 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | lazy_delta | 5,600 | 1,965.570 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[4] | gateway/component candidate | aggregate | application | 59,764 | 1,894.052 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[2] | gateway/component candidate | aggregate | quick | 79,841 | 1,567.146 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
