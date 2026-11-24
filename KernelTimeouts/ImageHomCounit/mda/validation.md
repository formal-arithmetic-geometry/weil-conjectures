# ImageHomCounit MDA validation

Root 2129: 6,359,958 calls; 117,357.356 ms comparison-exclusive; labels {'M0': 1, 'M1': 4781271, 'M2': 276, 'Matched': 1578409, 'Unclassified': 1}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 2129:1 | 0 | unattributed/fallback | `7` / `7`; Expr in JSONL | `unknown` | 4,781,271 | 117,357.356 | trace; nested rows overlap |
| 2129:2 | 1 | quick/dependent-body[6] | `Eq` / `Eq`; Expr in JSONL | `unknown` | 4,781,271 | 117,216.023 | trace; nested rows overlap |
| 2129:213 | 2 | application/argument[1] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 4,780,608 | 117,069.937 | trace; nested rows overlap |
| 2129:214 | 213 | second_whnf/whnf-iota-exposure | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 4,780,607 | 116,725.626 | trace; nested rows overlap |
| 2129:215 | 214 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 4,780,607 | 116,415.225 | trace; nested rows overlap |
| 2129:216 | 215 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 4,780,606 | 116,124.456 | trace; nested rows overlap |
| 2129:222 | 216 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 4,780,601 | 115,847.447 | trace; nested rows overlap |
| 2129:223 | 222 | second_whnf/whnf-iota-exposure | `CategoryTheory.MorphismProperty.instCategoryLocalization._aux_5` / `CategoryTheory.MorphismProperty.instCategoryLocalization._aux_5`; Expr in JSONL | `unknown` | 4,780,600 | 115,582.003 | trace; nested rows overlap |
| 2129:260 | 223 | lazy_delta/argument[6] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 4,780,575 | 115,173.961 | trace; nested rows overlap |
| 2129:261 | 260 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 4,780,574 | 115,035.886 | trace; nested rows overlap |
| 2129:262 | 261 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 4,780,573 | 114,931.076 | trace; nested rows overlap |
| 2129:263 | 262 | second_whnf/whnf-iota-exposure | `Equiv.invFun` / `Equiv.invFun`; Expr in JSONL | `unknown` | 4,780,572 | 114,838.174 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 511,341 | 54,131.260 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 1,253,595 | 19,616.924 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 421,702 | 11,934.034 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 423,631 | 4,590.544 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 252,270 | 3,658.265 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | lazy_delta | 184 | 3,614.609 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 898,770 | 3,338.050 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 121,429 | 1,845.694 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | lazy_delta | 4,757 | 1,591.992 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[2] | gateway/component candidate | aggregate | quick | 76,633 | 1,547.442 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[4] | gateway/component candidate | aggregate | application | 56,841 | 1,194.654 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[3] | gateway/component candidate | aggregate | quick | 43,624 | 736.315 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
