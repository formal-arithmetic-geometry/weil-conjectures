# PR2122 MDA validation

Root 36801: 2,227,198 calls; 23,180.333 ms comparison-exclusive; labels {'M0': 1, 'M1': 1749276, 'M2': 12631, 'Matched': 464966, 'Unclassified': 324}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 36801:1 | 0 | unattributed/fallback | `Eq` / `Eq`; Expr in JSONL | `unknown` | 1,749,276 | 23,180.333 | trace; nested rows overlap |
| 36801:1206456 | 1 | application/argument[2] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 819,137 | 8,591.496 | trace; nested rows overlap |
| 36801:1206457 | 1206456 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 819,137 | 8,496.954 | trace; nested rows overlap |
| 36801:339957 | 1 | application/argument[1] | `AlgebraicGeometry.ProEtale.SpTowerClasses.mapSingleArrow` / `AlgebraicGeometry.ProEtale.SpTowerClasses.mapSingleArrow`; Expr in JSONL | `unknown` | 652,939 | 8,488.235 | trace; nested rows overlap |
| 36801:339958 | 339957 | lazy_delta/argument[15] | `CategoryTheory.Abelian.Ext.hom` / `CategoryTheory.Abelian.Ext.hom`; Expr in JSONL | `unknown` | 652,931 | 8,487.242 | trace; nested rows overlap |
| 36801:339959 | 339958 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `unknown` | 652,931 | 8,477.572 | trace; nested rows overlap |
| 36801:339960 | 339959 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 652,930 | 8,474.005 | trace; nested rows overlap |
| 36801:1206458 | 1206457 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `unknown` | 819,136 | 8,406.853 | trace; nested rows overlap |
| 36801:339961 | 339960 | second_whnf/whnf-iota-exposure | `Function.comp` / `Function.comp`; Expr in JSONL | `unknown` | 652,929 | 8,223.938 | trace; nested rows overlap |
| 36801:3 | 1 | application/argument[0] | `Quiver.Hom` / `Quiver.Hom`; Expr in JSONL | `unknown` | 277,200 | 6,076.061 | trace; nested rows overlap |
| 36801:5 | 3 | application/argument[0] | `Quiver.Hom` / `Quiver.Hom`; Expr in JSONL | `unknown` | 277,197 | 6,074.891 | trace; nested rows overlap |
| 36801:1546366 | 1206458 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 541,942 | 5,957.386 | trace; nested rows overlap |
| 36801:6 | 5 | lazy_delta/argument[4] | `CategoryTheory.ShrinkHoms.fromShrinkHoms` / `CategoryTheory.ShrinkHoms.fromShrinkHoms`; Expr in JSONL | `unknown` | 138,599 | 4,826.920 | trace; nested rows overlap |
| 36801:7 | 6 | lazy_delta/argument[1] | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 138,598 | 4,826.371 | trace; nested rows overlap |
| 36801:9 | 7 | application/argument[0] | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 138,597 | 4,825.855 | trace; nested rows overlap |
| 36801:10 | 9 | lazy_delta/argument[1] | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 138,596 | 4,825.035 | trace; nested rows overlap |
| 36801:15 | 10 | application/argument[3] | `Prefunctor.obj` / `Prefunctor.obj`; Expr in JSONL | `unknown` | 138,596 | 4,822.400 | trace; nested rows overlap |
| 36801:20 | 15 | application/argument[3] | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 138,595 | 4,821.569 | trace; nested rows overlap |
| 36801:722136 | 339961 | lazy_delta/argument[3] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 364,825 | 4,405.750 | trace; nested rows overlap |
| 36801:1546367 | 1546366 | lazy_delta/argument[7] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `unknown` | 416,063 | 4,379.918 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 482,314 | 6,254.987 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 168,474 | 4,396.035 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 172,002 | 2,674.839 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 182,190 | 1,809.888 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 88,920 | 1,341.259 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 33,472 | 896.116 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 314,842 | 891.591 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | lazy_delta | 23,684 | 565.770 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[4] | gateway/component candidate | aggregate | application | 22,508 | 517.639 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[2] | gateway/component candidate | aggregate | quick | 17,875 | 454.091 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[5] | gateway/component candidate | aggregate | application | 19,538 | 337.062 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[1] | gateway/component candidate | aggregate | quick | 14,975 | 315.078 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | lazy_delta | 6,684 | 283.766 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[3] | gateway/component candidate | aggregate | application | 19,353 | 243.481 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | application | 5,976 | 236.088 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[3] | gateway/component candidate | aggregate | quick | 8,334 | 205.706 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[5] | gateway/component candidate | aggregate | lazy_delta | 9,250 | 188.428 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[8] | gateway/component candidate | aggregate | application | 2,877 | 154.144 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[3] | gateway/component candidate | aggregate | lazy_delta | 7,970 | 150.295 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | lazy_delta | 4,546 | 146.238 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
