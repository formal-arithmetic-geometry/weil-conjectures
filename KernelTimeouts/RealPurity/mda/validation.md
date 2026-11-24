# RealPurity MDA validation

Root 13603: 17,310,168 calls; 103,491.083 ms comparison-exclusive; labels {'M0': 1, 'M1': 7988264, 'M2': 4357093, 'Matched': 4964810}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 13603:1 | 0 | unattributed/fallback | `Eq` / `Eq`; Expr in JSONL | `unknown` | 7,988,264 | 103,491.083 | trace; nested rows overlap |
| 13603:4 | 1 | application/argument[1] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 7,988,264 | 103,490.745 | trace; nested rows overlap |
| 13603:5 | 4 | second_whnf/whnf-iota-exposure | `OneHom.toFun` / `OneHom.toFun`; Expr in JSONL | `unknown` | 7,988,263 | 103,490.412 | trace; nested rows overlap |
| 13603:6 | 5 | second_whnf/whnf-iota-exposure | `Star.star` / `Star.star`; Expr in JSONL | `unknown` | 7,988,262 | 103,490.095 | trace; nested rows overlap |
| 13603:7 | 6 | second_whnf/whnf-iota-exposure | `Complex.mk` / `Complex.mk`; Expr in JSONL | `unknown` | 7,988,261 | 103,489.501 | trace; nested rows overlap |
| 13603:9 | 7 | application/argument[0] | `Complex.re` / `Complex.re`; Expr in JSONL | `unknown` | 7,988,260 | 103,489.184 | trace; nested rows overlap |
| 13603:10 | 9 | projection/projection[0] | `DFunLike.proj` / `DFunLike.proj`; Expr in JSONL | `unknown` | 7,988,259 | 103,488.886 | trace; nested rows overlap |
| 13603:11 | 10 | second_whnf/whnf-iota-exposure | `OneHom.toFun` / `OneHom.toFun`; Expr in JSONL | `unknown` | 7,988,258 | 103,488.538 | trace; nested rows overlap |
| 13603:13 | 11 | application/argument[0] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 7,988,257 | 103,488.189 | trace; nested rows overlap |
| 13603:14 | 13 | second_whnf/whnf-iota-exposure | `Finsupp.toFun` / `Finsupp.toFun`; Expr in JSONL | `unknown` | 7,988,256 | 103,487.857 | trace; nested rows overlap |
| 13603:15 | 14 | second_whnf/whnf-iota-exposure | `Finsupp.embDomain.match_1` / `Finsupp.embDomain.match_1`; Expr in JSONL | `unknown` | 7,988,255 | 103,356.298 | trace; nested rows overlap |
| 13603:32 | 15 | application/argument[3] | `6` / `6`; Expr in JSONL | `unknown` | 7,988,252 | 103,038.123 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[1] | gateway/component candidate | aggregate | quick | 1,439,853 | 23,260.620 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / projection[0] | gateway/component candidate | aggregate | projection | 4,288,238 | 20,650.526 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[2] | gateway/component candidate | aggregate | application | 256,945 | 6,932.217 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[4] | gateway/component candidate | aggregate | application | 530,913 | 5,055.265 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / function-head | gateway/component candidate | aggregate | application | 1,428,222 | 5,039.216 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 103 | 1,100.048 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[3] | gateway/component candidate | aggregate | quick | 5,744 | 977.978 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[2] | gateway/component candidate | aggregate | quick | 11,488 | 496.573 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[3] | gateway/component candidate | aggregate | application | 22,976 | 331.032 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 46 | 164.145 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 20 | 106.488 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[1] | gateway/component candidate | aggregate | quick | 18 | 94.249 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
