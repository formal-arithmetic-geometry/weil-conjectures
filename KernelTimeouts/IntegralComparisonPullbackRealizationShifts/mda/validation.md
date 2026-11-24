# IntegralComparison MDA validation

Root 24513: 9,426,253 calls; 139,130.382 ms comparison-exclusive; labels {'M0': 1, 'M1': 6680881, 'M2': 25204, 'Matched': 2720167}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 24513:1 | 0 | unattributed/fallback | `Eq` / `Eq`; Expr in JSONL | `unknown` | 6,680,881 | 139,130.382 | trace; nested rows overlap |
| 24513:68 | 1 | application/argument[2] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 6,680,850 | 139,003.851 | trace; nested rows overlap |
| 24513:69 | 68 | lazy_delta/argument[7] | `CategoryTheory.NatTrans.app` / `CategoryTheory.NatTrans.app`; Expr in JSONL | `unknown` | 6,680,835 | 138,983.009 | trace; nested rows overlap |
| 24513:70 | 69 | second_whnf/whnf-iota-exposure | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 6,680,835 | 138,908.194 | trace; nested rows overlap |
| 24513:73 | 72 | lazy_delta/argument[7] | `CategoryTheory.NatTrans.app` / `CategoryTheory.NatTrans.app`; Expr in JSONL | `unknown` | 3,326,676 | 81,423.905 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 1,939,882 | 34,756.262 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 481,400 | 27,014.786 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | lazy_delta | 7,697 | 10,465.324 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[9] | gateway/component candidate | aggregate | lazy_delta | 29,178 | 9,565.120 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 1,258,058 | 9,302.795 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 494,403 | 5,971.105 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 362,023 | 4,800.030 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[8] | gateway/component candidate | aggregate | lazy_delta | 390 | 3,901.159 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 572,466 | 3,489.484 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 167,994 | 3,232.628 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[5] | gateway/component candidate | aggregate | lazy_delta | 88,165 | 2,639.306 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | lazy_delta | 28,454 | 2,578.083 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
