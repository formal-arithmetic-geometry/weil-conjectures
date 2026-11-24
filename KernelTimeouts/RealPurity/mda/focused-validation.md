# RealPurityFocus MDA validation

Root 13603: 17,310,168 calls; 97,452.965 ms comparison-exclusive; labels {'M0': 1, 'M1': 7988264, 'M2': 4357093, 'Matched': 4964810}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 13603:1 | 0 | unattributed/fallback | `Eq` / `Eq`; Expr in JSONL | `unknown` | 7,988,264 | 97,452.965 | trace; nested rows overlap |
| 13603:4 | 1 | application/argument[1] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 7,988,264 | 97,452.583 | trace; nested rows overlap |
| 13603:15 | 14 | second_whnf/whnf-iota-exposure | `Finsupp.embDomain.match_1` / `Finsupp.embDomain.match_1`; Expr in JSONL | `unknown` | 7,988,255 | 97,319.589 | trace; nested rows overlap |
| 13603:32 | 15 | application/argument[3] | `6` / `6`; Expr in JSONL | `unknown` | 7,988,252 | 97,006.078 | trace; nested rows overlap |
| 13603:38 | 37 | projection/projection[0] | `MultilinearMap.proj` / `MultilinearMap.proj`; Expr in JSONL | `unknown` | 7,988,246 | 96,746.690 | trace; nested rows overlap |
| 13603:575 | 38 | application/argument[0] | `Matrix.charmatrix` / `Matrix.charmatrix`; Expr in JSONL | `unknown` | 7,987,934 | 95,636.387 | trace; nested rows overlap |
| 13603:916 | 912 | application/argument[2] | `Quiver.Hom` / `Quiver.Hom`; Expr in JSONL | `unknown` | 7,987,786 | 94,887.059 | trace; nested rows overlap |
| 13603:920 | 916 | application/argument[2] | `AlgebraicGeometry.WeilSheaf.stalkObj` / `AlgebraicGeometry.WeilSheaf.stalkObj`; Expr in JSONL | `AlgebraicGeometry.WeilSheaf.stalkObj` | 7,987,785 | 94,886.846 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / projection[0] | gateway/component candidate | aggregate | projection | 4,288,238 | 20,469.596 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[1] | gateway/component candidate | aggregate | quick | 1,439,853 | 20,385.597 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[2] | gateway/component candidate | aggregate | application | 256,945 | 5,456.399 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / function-head | gateway/component candidate | aggregate | application | 1,428,222 | 5,057.640 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[4] | gateway/component candidate | aggregate | application | 530,913 | 4,812.592 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 103 | 1,205.923 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[2] | gateway/component candidate | aggregate | quick | 11,488 | 487.746 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / dependent-body[3] | gateway/component candidate | aggregate | quick | 5,744 | 464.923 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.WeilSheaf.stalkObj` / argument[3] | gateway/component candidate | aggregate | application | 22,976 | 335.348 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 46 | 237.339 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 20 | 171.814 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[1] | gateway/component candidate | aggregate | quick | 18 | 112.129 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
