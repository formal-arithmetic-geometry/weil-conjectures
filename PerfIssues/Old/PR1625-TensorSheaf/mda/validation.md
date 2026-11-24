# PR1625 MDA validation

Root 79312: 11,757,800 calls; 158,646.806 ms comparison-exclusive; labels {'M0': 1, 'M1': 8111031, 'M2': 4686, 'Matched': 3642050, 'Unclassified': 32}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 79312:1 | 0 | unattributed/fallback | `7` / `7`; Expr in JSONL | `unknown` | 8,111,031 | 158,646.806 | trace; nested rows overlap |
| 79312:2 | 1 | quick/dependent-body[15] | `Eq` / `Eq`; Expr in JSONL | `unknown` | 8,111,031 | 158,262.189 | trace; nested rows overlap |
| 79312:44 | 2 | application/argument[1] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 8,022,115 | 157,029.412 | trace; nested rows overlap |
| 79312:45 | 44 | second_whnf/whnf-iota-exposure | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 8,022,114 | 155,630.800 | trace; nested rows overlap |
| 79312:46 | 45 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 8,022,113 | 154,430.127 | trace; nested rows overlap |
| 79312:47 | 46 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 8,022,112 | 153,402.588 | trace; nested rows overlap |
| 79312:53 | 47 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 8,022,107 | 152,464.537 | trace; nested rows overlap |
| 79312:54 | 53 | second_whnf/whnf-iota-exposure | `CategoryTheory.MorphismProperty.instCategoryLocalization._aux_5` / `CategoryTheory.MorphismProperty.instCategoryLocalization._aux_5`; Expr in JSONL | `unknown` | 8,022,106 | 151,631.556 | trace; nested rows overlap |
| 79312:93 | 54 | lazy_delta/argument[6] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 8,022,087 | 149,571.862 | trace; nested rows overlap |
| 79312:94 | 93 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 8,022,086 | 149,497.059 | trace; nested rows overlap |
| 79312:95 | 94 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 8,022,085 | 149,439.280 | trace; nested rows overlap |
| 79312:96 | 95 | second_whnf/whnf-iota-exposure | `Equiv.invFun` / `Equiv.invFun`; Expr in JSONL | `unknown` | 8,022,084 | 149,388.818 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 543,348 | 41,252.430 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 1,629,258 | 31,046.339 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 1,067,015 | 15,076.916 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 1,141,455 | 13,900.454 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 1,311,959 | 9,304.662 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 322,571 | 8,238.511 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[3] | gateway/component candidate | aggregate | quick | 93,092 | 5,010.132 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | lazy_delta | 70,058 | 4,565.794 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 139,130 | 3,062.481 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | application | 97,392 | 3,005.658 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[3] | gateway/component candidate | aggregate | application | 185,288 | 2,357.895 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[4] | gateway/component candidate | aggregate | application | 278,124 | 2,271.894 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
