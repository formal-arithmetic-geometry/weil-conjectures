# EtaleHom MDA validation

Root 2632: 3,180,470 calls; 30,519.102 ms comparison-exclusive; labels {'M0': 1, 'M1': 2390795, 'M2': 22, 'Matched': 789652}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 2632:1 | 0 | unattributed/fallback | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / `7`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,795 | 30,519.102 | trace; nested rows overlap |
| 2632:3 | 1 | quick/dependent-body[1] | `Eq` / `Eq`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,794 | 30,438.540 | trace; nested rows overlap |
| 2632:709 | 3 | application/argument[2] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,536 | 30,278.941 | trace; nested rows overlap |
| 2632:710 | 709 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,535 | 30,242.470 | trace; nested rows overlap |
| 2632:711 | 710 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,534 | 30,216.179 | trace; nested rows overlap |
| 2632:712 | 711 | second_whnf/whnf-iota-exposure | `Equiv.invFun` / `Equiv.invFun`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,533 | 30,197.613 | trace; nested rows overlap |
| 2632:713 | 712 | second_whnf/whnf-iota-exposure | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,532 | 30,174.445 | trace; nested rows overlap |
| 2632:714 | 713 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,531 | 29,863.139 | trace; nested rows overlap |
| 2632:715 | 714 | second_whnf/whnf-iota-exposure | `Equiv.toFun` / `Equiv.toFun`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,530 | 29,574.193 | trace; nested rows overlap |
| 2632:1334 | 715 | application/argument[0] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,324 | 29,298.666 | trace; nested rows overlap |
| 2632:1335 | 1334 | lazy_delta/argument[7] | `DFunLike.coe` / `DFunLike.coe`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,295 | 29,199.059 | trace; nested rows overlap |
| 2632:1336 | 1335 | second_whnf/whnf-iota-exposure | `EquivLike.coe` / `EquivLike.coe`; Expr in JSONL | `AlgebraicGeometry.Etale.IsEtaleHomTranspose` | 2,390,294 | 29,135.796 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / projection[0] | gateway/component candidate | aggregate | projection | 626,927 | 9,744.225 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 255,583 | 6,564.525 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / argument[1] | gateway/component candidate | aggregate | application | 211,855 | 2,952.623 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / function-head | gateway/component candidate | aggregate | application | 449,473 | 1,750.894 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / argument[0] | gateway/component candidate | aggregate | application | 210,787 | 1,544.842 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / argument[2] | gateway/component candidate | aggregate | application | 126,185 | 1,477.603 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 60,717 | 937.566 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / dependent-body[2] | gateway/component candidate | aggregate | quick | 38,329 | 700.133 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / argument[4] | gateway/component candidate | aggregate | application | 28,438 | 660.421 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / dependent-body[1] | gateway/component candidate | aggregate | quick | 13,324 | 436.292 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / argument[1] | gateway/component candidate | aggregate | lazy_delta | 6,933 | 377.848 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.Etale.IsEtaleHomTranspose` / dependent-body[3] | gateway/component candidate | aggregate | quick | 21,825 | 376.030 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
