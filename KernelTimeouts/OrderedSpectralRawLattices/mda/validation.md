# OrderedSpectralRawLattices MDA validation

Root 62844: 18,944,709 calls; 99,604.149 ms comparison-exclusive; labels {'M0': 1, 'M1': 8320909, 'M2': 3499646, 'Matched': 7124151, 'Unclassified': 2}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 62844:1 | 0 | unattributed/fallback | `7` / `7`; Expr in JSONL | `unknown` | 8,320,909 | 99,604.149 | trace; nested rows overlap |
| 62844:2 | 1 | quick/dependent-body[17] | `8` / `8`; Expr in JSONL | `unknown` | 8,320,909 | 99,512.219 | trace; nested rows overlap |
| 62844:5028 | 2 | quick/dependent-body[2] | `Exists` / `Exists`; Expr in JSONL | `unknown` | 8,319,002 | 98,899.195 | trace; nested rows overlap |
| 62844:5031 | 5028 | application/argument[1] | `6` / `6`; Expr in JSONL | `unknown` | 8,319,002 | 98,447.342 | trace; nested rows overlap |
| 62844:5032 | 5031 | quick/dependent-body[1] | `7` / `7`; Expr in JSONL | `unknown` | 8,319,001 | 97,978.713 | trace; nested rows overlap |
| 62844:5033 | 5032 | quick/dependent-body[1] | `8` / `Exists`; Expr in JSONL | `unknown` | 8,319,001 | 97,533.783 | trace; nested rows overlap |
| 62844:8203 | 5033 | application/argument[1] | `6` / `6`; Expr in JSONL | `unknown` | 8,317,853 | 96,994.271 | trace; nested rows overlap |
| 62844:8205 | 8203 | quick/dependent-body[1] | `And` / `And`; Expr in JSONL | `unknown` | 8,317,851 | 96,464.191 | trace; nested rows overlap |
| 62844:9851 | 8205 | application/argument[1] | `Exists` / `Exists`; Expr in JSONL | `unknown` | 8,317,217 | 95,948.499 | trace; nested rows overlap |
| 62844:9853 | 9851 | application/argument[0] | `Quiver.Hom` / `Quiver.Hom`; Expr in JSONL | `unknown` | 8,317,216 | 95,924.432 | trace; nested rows overlap |
| 62844:9854 | 9853 | second_whnf/whnf-iota-exposure | `CategoryTheory.Mod.Hom` / `CategoryTheory.Mod.Hom`; Expr in JSONL | `unknown` | 8,317,215 | 95,903.811 | trace; nested rows overlap |
| 62844:9865 | 9854 | application/argument[9] | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 8,317,213 | 95,885.021 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `AlgebraicGeometry.ProEtale.toSpecZ` / projection[0] | gateway/component candidate | aggregate | projection | 3,623,811 | 18,760.864 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.toSpecZ` / argument[0] | gateway/component candidate | aggregate | application | 1,058,814 | 15,704.319 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.toSpecZ` / dependent-body[1] | gateway/component candidate | aggregate | quick | 483,172 | 15,157.284 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.toSpecZ` / argument[2] | gateway/component candidate | aggregate | application | 363,844 | 3,981.849 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.toSpecZ` / argument[4] | gateway/component candidate | aggregate | application | 268,430 | 3,535.369 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.toSpecZ` / argument[5] | gateway/component candidate | aggregate | application | 724,759 | 3,116.261 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.upperStar._proof_1` / dependent-body[3] | gateway/component candidate | aggregate | quick | 2,911 | 1,264.644 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 35 | 1,023.483 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[1] | gateway/component candidate | aggregate | quick | 1 | 506.539 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[17] | gateway/component candidate | aggregate | quick | 1 | 472.314 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.upperStar._proof_1` / dependent-body[2] | gateway/component candidate | aggregate | quick | 5,822 | 464.714 | not tested in Batch 0 | aggregate, attribution provisional |
| `AlgebraicGeometry.ProEtale.upperStar._proof_1` / dependent-body[1] | gateway/component candidate | aggregate | quick | 5,899 | 453.834 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
