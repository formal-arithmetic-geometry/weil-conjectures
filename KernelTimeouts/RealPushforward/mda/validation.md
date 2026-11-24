# RealPushforward MDA validation

Root 2005: 17,340,236 calls; 95,517.663 ms comparison-exclusive; labels {'M0': 1, 'M1': 8002209, 'M2': 4364762, 'Matched': 4973262, 'Unclassified': 2}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 2005:1 | 0 | unattributed/fallback | `7` / `7`; Expr in JSONL | `unknown` | 8,002,209 | 95,517.663 | trace; nested rows overlap |
| 2005:3 | 1 | quick/dependent-body[2] | `Eq` / `5`; Expr in JSONL | `unknown` | 8,002,209 | 95,514.273 | trace; nested rows overlap |
| 2005:6 | 3 | application/argument[1] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 8,002,209 | 95,513.891 | trace; nested rows overlap |
| 2005:8 | 6 | application/argument[0] | `Complex.re` / `Complex.re`; Expr in JSONL | `unknown` | 8,002,209 | 95,513.538 | trace; nested rows overlap |
| 2005:9 | 8 | projection/projection[0] | `OneHom.proj` / `OneHom.proj`; Expr in JSONL | `unknown` | 8,002,208 | 95,513.193 | trace; nested rows overlap |
| 2005:11 | 9 | application/argument[0] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 8,002,207 | 95,512.791 | trace; nested rows overlap |
| 2005:12 | 11 | second_whnf/whnf-iota-exposure | `Finsupp.embDomain.match_1` / `Finsupp.embDomain.match_1`; Expr in JSONL | `unknown` | 8,002,206 | 95,314.462 | trace; nested rows overlap |
| 2005:29 | 12 | application/argument[3] | `6` / `6`; Expr in JSONL | `unknown` | 8,002,203 | 94,857.091 | trace; nested rows overlap |
| 2005:30 | 29 | quick/dependent-body[1] | `5` / `5`; Expr in JSONL | `unknown` | 8,002,202 | 94,793.397 | trace; nested rows overlap |
| 2005:31 | 30 | application/function-head | `Finsupp.proj` / `Finsupp.proj`; Expr in JSONL | `unknown` | 8,002,201 | 94,730.112 | trace; nested rows overlap |
| 2005:32 | 31 | projection/projection[0] | `AddMonoidAlgebra.proj` / `AddMonoidAlgebra.proj`; Expr in JSONL | `unknown` | 8,002,200 | 94,665.592 | trace; nested rows overlap |
| 2005:33 | 32 | projection/projection[0] | `Polynomial.proj` / `Polynomial.proj`; Expr in JSONL | `unknown` | 8,002,199 | 94,602.521 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / projection[0] | gateway/component candidate | aggregate | projection | 4,295,783 | 20,329.770 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[1] | gateway/component candidate | aggregate | quick | 1,442,386 | 18,831.830 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[2] | gateway/component candidate | aggregate | application | 257,395 | 5,416.363 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / function-head | gateway/component candidate | aggregate | application | 1,430,735 | 5,027.964 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[4] | gateway/component candidate | aggregate | application | 531,847 | 4,783.240 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 59 | 1,014.253 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[2] | gateway/component candidate | aggregate | quick | 11,508 | 481.703 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[3] | gateway/component candidate | aggregate | quick | 5,754 | 453.077 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[3] | gateway/component candidate | aggregate | application | 23,016 | 294.982 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 15 | 240.961 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 17 | 230.417 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 22 | 151.349 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
