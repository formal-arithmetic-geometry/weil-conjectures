# RealPushforwardObject MDA validation

Root 2005: 17,340,236 calls; 96,755.372 ms comparison-exclusive; labels {'M0': 1, 'M1': 8002209, 'M2': 4364762, 'Matched': 4973262, 'Unclassified': 2}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 2005:1 | 0 | unattributed/fallback | `7` / `7`; Expr in JSONL | `unknown` | 8,002,209 | 96,755.372 | trace; nested rows overlap |
| 2005:3 | 1 | quick/dependent-body[2] | `Eq` / `5`; Expr in JSONL | `unknown` | 8,002,209 | 96,751.949 | trace; nested rows overlap |
| 2005:6 | 3 | application/argument[1] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 8,002,209 | 96,751.529 | trace; nested rows overlap |
| 2005:12 | 11 | second_whnf/whnf-iota-exposure | `Finsupp.embDomain.match_1` / `Finsupp.embDomain.match_1`; Expr in JSONL | `unknown` | 8,002,206 | 96,560.138 | trace; nested rows overlap |
| 2005:33 | 32 | projection/projection[0] | `Polynomial.proj` / `Polynomial.proj`; Expr in JSONL | `unknown` | 8,002,199 | 95,852.171 | trace; nested rows overlap |
| 2005:34 | 33 | projection/projection[0] | `MultilinearMap.proj` / `MultilinearMap.proj`; Expr in JSONL | `unknown` | 8,002,198 | 95,789.418 | trace; nested rows overlap |
| 2005:484 | 34 | application/argument[0] | `Matrix.charmatrix` / `Matrix.charmatrix`; Expr in JSONL | `unknown` | 8,001,876 | 94,094.131 | trace; nested rows overlap |
| 2005:531 | 527 | application/argument[2] | `Quiver.Hom` / `Quiver.Hom`; Expr in JSONL | `unknown` | 8,001,839 | 93,204.984 | trace; nested rows overlap |
| 2005:535 | 531 | application/argument[2] | `AlgebraicGeometry.WeilSheaf.stalkObj` / `AlgebraicGeometry.WeilSheaf.stalkObj`; Expr in JSONL | `AlgebraicGeometry.WeilSheaf.stalkObj` | 8,001,838 | 93,204.737 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / projection[0] | gateway/component candidate | aggregate | projection | 4,295,783 | 20,313.663 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[1] | gateway/component candidate | aggregate | quick | 1,442,386 | 19,019.357 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[2] | gateway/component candidate | aggregate | application | 257,395 | 5,385.965 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / function-head | gateway/component candidate | aggregate | application | 1,430,735 | 5,012.249 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[4] | gateway/component candidate | aggregate | application | 531,847 | 4,806.784 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 59 | 1,100.318 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[2] | gateway/component candidate | aggregate | quick | 11,508 | 487.399 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[3] | gateway/component candidate | aggregate | quick | 5,754 | 468.586 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 22 | 329.167 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[3] | gateway/component candidate | aggregate | application | 23,016 | 309.520 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 17 | 283.476 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 15 | 254.930 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
