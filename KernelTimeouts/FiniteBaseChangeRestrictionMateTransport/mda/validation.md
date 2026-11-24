# FiniteBaseChange MDA validation

Root 16563: 239,340,712 calls; 1,239,204.129 ms comparison-exclusive; labels {'M0': 1, 'M1': 130197227, 'M2': 40495866, 'Matched': 68647618}. All group and transition sums reconcile.

## 4.1 Gateway-to-cost

| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| 16563:1 | 0 | unattributed/fallback | `7` / `7`; Expr in JSONL | `unknown` | 130,197,227 | 1,239,204.129 | trace; nested rows overlap |
| 16563:2 | 1 | quick/dependent-body[1] | `Eq` / `Eq`; Expr in JSONL | `unknown` | 130,197,227 | 1,238,807.422 | trace; nested rows overlap |
| 16563:7823 | 2 | application/argument[2] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 130,191,839 | 1,233,203.176 | trace; nested rows overlap |
| 16563:7924 | 7823 | application/argument[6] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 130,191,810 | 1,233,043.154 | trace; nested rows overlap |
| 16563:7935 | 7924 | application/argument[5] | `6` / `6`; Expr in JSONL | `unknown` | 130,186,708 | 1,232,797.932 | trace; nested rows overlap |
| 16563:7936 | 7935 | quick/dependent-body[1] | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 130,186,707 | 1,232,605.577 | trace; nested rows overlap |
| 16563:7937 | 7936 | second_whnf/whnf-iota-exposure | `ModuleCat.Hom._mkInternal` / `ModuleCat.Hom._mkInternal`; Expr in JSONL | `unknown` | 130,186,706 | 1,232,236.300 | trace; nested rows overlap |
| 16563:8492 | 7937 | application/argument[4] | `LinearMap.comp` / `LinearMap.comp`; Expr in JSONL | `unknown` | 130,186,385 | 1,231,891.861 | trace; nested rows overlap |
| 16563:8493 | 8492 | lazy_delta/argument[20] | `ModuleCat.Hom.hom'` / `ModuleCat.Hom.hom'`; Expr in JSONL | `unknown` | 130,186,143 | 1,231,842.933 | trace; nested rows overlap |
| 16563:8494 | 8493 | projection/projection[0] | `PresheafOfModules.Hom.proj` / `PresheafOfModules.Hom.proj`; Expr in JSONL | `unknown` | 130,186,142 | 1,231,825.045 | trace; nested rows overlap |
| 16563:8495 | 8494 | application/function-head | `PresheafOfModules.Hom.proj` / `PresheafOfModules.Hom.proj`; Expr in JSONL | `unknown` | 130,186,141 | 1,231,807.054 | trace; nested rows overlap |
| 16563:8496 | 8495 | projection/projection[0] | `SheafOfModules.Hom.proj` / `SheafOfModules.Hom.proj`; Expr in JSONL | `unknown` | 130,186,140 | 1,231,799.735 | trace; nested rows overlap |
| 16563:8497 | 8496 | projection/projection[0] | `CategoryTheory.Functor.proj` / `CategoryTheory.Functor.proj`; Expr in JSONL | `unknown` | 130,186,139 | 1,231,793.696 | trace; nested rows overlap |
| 16563:8530 | 8497 | application/argument[2] | `CategoryTheory.NatTrans.app` / `CategoryTheory.NatTrans.app`; Expr in JSONL | `unknown` | 130,186,131 | 1,231,791.290 | trace; nested rows overlap |
| 16563:8531 | 8530 | second_whnf/whnf-iota-exposure | `CategoryTheory.CategoryStruct.comp` / `CategoryTheory.CategoryStruct.comp`; Expr in JSONL | `unknown` | 130,186,131 | 1,231,779.522 | trace; nested rows overlap |

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | Direct calls | M1 exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `unknown` / dependent-body[1] | gateway/component candidate | aggregate | quick | 19,907,361 | 330,838.233 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / projection[0] | gateway/component candidate | aggregate | projection | 98,782,787 | 329,175.321 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / field[0] | gateway/component candidate | aggregate | eta_structure | 19,741,562 | 297,236.093 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[2] | gateway/component candidate | aggregate | application | 11,249,671 | 93,321.462 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[4] | gateway/component candidate | aggregate | application | 7,377,734 | 71,729.805 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / function-head | gateway/component candidate | aggregate | application | 30,999,513 | 61,505.257 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[3] | gateway/component candidate | aggregate | quick | 79,596 | 13,539.368 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / dependent-body[2] | gateway/component candidate | aggregate | quick | 159,052 | 9,179.123 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / fallback | gateway/component candidate | aggregate | unattributed | 953,858 | 8,166.387 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / field | gateway/component candidate | aggregate | eta_structure | 19,741,562 | 6,933.791 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[3] | gateway/component candidate | aggregate | application | 7,695,738 | 6,531.228 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[1] | gateway/component candidate | aggregate | application | 11,251,420 | 2,603.315 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[0] | gateway/component candidate | aggregate | application | 11,253,307 | 2,382.222 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / argument[6] | gateway/component candidate | aggregate | application | 10,807 | 1,643.559 | not tested in Batch 0 | aggregate, attribution provisional |
| `unknown` / whnf-iota-exposure | gateway/component candidate | aggregate | second_whnf | 840 | 1,351.021 | not tested in Batch 0 | aggregate, attribution provisional |

Direct group times partition the root. Inclusive subtree times overlap; do not add them.
