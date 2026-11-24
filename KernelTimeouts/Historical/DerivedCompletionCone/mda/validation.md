# DerivedCompletionCone MDA validation

Root 1849: 12,220,822 calls; 123,760.785 ms comparison-exclusive; labels {'M0': 1, 'M1': 9356262, 'M2': 9087, 'Matched': 2855469, 'Unclassified': 3}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 1849:1 | 0 | unattributed/fallback | `7` / `7`; Expr in JSONL | `unknown` | 9,356,262 | 123,760.785 | trace; nested rows overlap |
| 1849:24 | 1 | quick/dependent-body[8] | `CategoryTheory.Limits.Cone` / `CategoryTheory.Limits.Cone`; Expr in JSONL | `unknown` | 9,356,257 | 123,757.103 | trace; nested rows overlap |
| 1849:34 | 24 | application/argument[4] | `CategoryTheory.Functor.comp` / `CategoryTheory.Functor.comp`; Expr in JSONL | `unknown` | 9,356,253 | 123,756.029 | trace; nested rows overlap |
| 1849:35 | 34 | lazy_delta/argument[7] | `CategoryTheory.MonoidalCategory.tensorLeft` / `CategoryTheory.MonoidalCategory.tensorLeft`; Expr in JSONL | `unknown` | 9,356,252 | 123,755.600 | trace; nested rows overlap |
| 1849:36 | 35 | second_whnf/whnf-iota-exposure | `CategoryTheory.Functor.mk` / `CategoryTheory.Functor.mk`; Expr in JSONL | `unknown` | 9,356,251 | 123,752.725 | trace; nested rows overlap |
| 1849:42 | 36 | application/argument[4] | `6` / `6`; Expr in JSONL | `unknown` | 9,356,246 | 123,751.854 | trace; nested rows overlap |
| 1849:44 | 42 | quick/dependent-body[1] | `CategoryTheory.MonoidalCategoryStruct.tensorObj` / `CategoryTheory.MonoidalCategoryStruct.tensorObj`; Expr in JSONL | `unknown` | 9,356,244 | 123,751.175 | trace; nested rows overlap |
| 1849:45 | 44 | second_whnf/whnf-iota-exposure | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 9,356,243 | 123,727.843 | trace; nested rows overlap |
| 1849:46 | 45 | second_whnf/whnf-iota-exposure | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 9,356,242 | 123,672.622 | trace; nested rows overlap |
| 1849:47 | 46 | application/function-head | `CategoryTheory.Functor.proj` / `CategoryTheory.Functor.proj`; Expr in JSONL | `unknown` | 9,356,241 | 123,626.438 | trace; nested rows overlap |
| 1849:197547 | 47 | lazy_delta/argument[6] | `CategoryTheory.Functor.obj` / `CategoryTheory.Functor.obj`; Expr in JSONL | `unknown` | 9,205,544 | 120,671.058 | trace; nested rows overlap |
| 1849:197548 | 197547 | second_whnf/whnf-iota-exposure | `CategoryTheory.Functor.mk` / `CategoryTheory.Functor.mk`; Expr in JSONL | `unknown` | 9,205,543 | 120,458.310 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 2,951,252 | 45,242.360 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 1,053,679 | 25,098.546 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 714,265 | 8,115.246 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 1,648,540 | 7,818.184 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 706,043 | 6,339.933 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 424,519 | 4,421.722 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / proposition-type | gateway/component candidate | aggregate | proof_irrelevance | 187,303 | 4,112.115 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[3] | gateway/component candidate | aggregate | quick | 14,552 | 3,646.357 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[4] | gateway/component candidate | aggregate | application | 126,501 | 3,346.148 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[2] | gateway/component candidate | aggregate | quick | 170,801 | 2,950.629 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | lazy_delta | 13,198 | 1,400.262 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[7] | gateway/component candidate | aggregate | application | 56,620 | 1,327.186 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
