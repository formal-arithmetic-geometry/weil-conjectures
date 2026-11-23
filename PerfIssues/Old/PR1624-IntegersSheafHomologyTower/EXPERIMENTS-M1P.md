# PR1624: M1 propagation (READY4.1)

## Original root and validity

The original `OriginalDependentEndpoint.lean` probe ran under READY4.1
Lean 4.35.0 with the source's transparency and synthesis options and a
3600 s limit. The selected process-wide root is 22078, the dependent
`CategoryTheory.Iso`/`CategoryTheory.Iso` endpoint. Its two `Functor.comp`
arguments are the first source-level divergent endpoint components.
The trace root completed with 6,598,545 calls, 43,944.883 ms
comparison-exclusive time, and 75,156.302 ms root wall. A separate fresh
counters run measured 6,598,545 calls, 55,517.435 ms root wall, and
28,306.603 ms comparison-exclusive time. The call count equals the accepted READY3.2 count;
the M1 share differs from its 99.804% by 0.022 percentage points.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.039 | <0.001% |
| M1 | 5,215,138 | 43,849.070 | 99.782% |
| M2 | 287 | 3.223 | 0.007% |
| Matched | 1,383,111 | 92.282 | 0.210% |
| Unclassified | 8 | 0.268 | 0.001% |

Analyzer revision: READY4.1 `mprwe_analyze.py`, kernel dataset commit
`5ae674db0c7`. Aggregate coverage is 6,598,545/6,598,545 calls. Raw
capture is 1,483 entered and 1,406 exited calls (0.0225% by entered
calls). Kernel aggregates classify every call and reconcile to the
43,944.883 ms root total: 6,598,544 child edges plus the 0.039 ms root
direct time. Each label's depth calls and exclusive/reduction time match
its label aggregate; no depth was clamped.

## A2: topology

M1 depth: mean 59.312, median 60, p90 70, p99 77, max 88. The narrowest
bands holding 50% and 90% of M1 exclusive time are depths 52-64 and
46-74. M1 depth histogram in ten-depth bins (start: calls/exclusive ms):
0:496/7.8; 10:1,291/14.4; 20:5,218/57.5; 30:85,677/683.4;
40:622,837/4,838.8; 50:1,811,233/14,761.2;
60:2,059,387/17,455.5; 70:614,732/5,894.3; 80:14,267/136.2.

M1-parent fan-out over all child labels: mean 1.265, median 1, p90 3,
max 21. Exact histogram (children:nodes): 0:1,848,124; 1:1,969,023;
2:531,073; 3:506,801; 4:254,200; 5:8,075; 6:32,891;
7:24,672; 8:113; 9:6,672; 10:782; 11:11; 13:5;
14:19,476; 21:13,220. Bounded raw capture observes 880 M1-to-M1,
471 M1-to-Matched, and 29 M1-to-M2 edges. The unchanged READY4.1 patch
does not aggregate complete parent-label by child-label edge counts;
these are sample counts only.

This is **mixed** propagation. There is substantial time at depths 50-70,
and repeated projection and application branching generates the bulk of
work. It is shallower than PR1556/PR1625, but neither a single chain nor
a shallow flat fan-out.

## A3: branch transition matrix

Rows cover all child labels. The top four hold 39,766.773 ms (90.49% of
root exclusive time); even subtracting all 95.813 ms of non-M1 time,
these rows include more than 90% of M1 exclusive time. Mean fan-out by
branch is not emitted; the full M1-parent mean is above.

| Parent branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 1,296,272 | 17,618.951 |
| application | argument | 2,640,249 | 12,710.696 |
| second_whnf | fallback | 533,577 | 5,740.946 |
| application | function-head | 1,223,984 | 3,696.180 |
| quick | dependent-body | 150,818 | 2,094.288 |
| proof_irrelevance | proposition-type | 125,785 | 1,084.550 |
| lazy_delta | argument | 318,055 | 783.489 |
| remaining rows | mixed | 309,804 | 215.744 |

The largest aggregate M1 bucket is `__other__` (1,712,301 calls;
12,731.140 ms). The highest *named* paths are
`root/argument[3]/argument[5]/binder_body[3]/argument[5]/argument[8]/*`
(670,667 calls; 6,633.444 ms),
`root/argument[2]/argument[7]/proposition_type/binder_body[5]/argument[2]/*`
(670,811; 5,799.375 ms), and its `argument[0]` sibling
(447,020; 4,210.092 ms). `__other__` and `*` are bounded path groups,
not individual inclusive subtrees.

## A4: first transitions of named costly paths

The M0 pair is `Iso`/`Iso`. Its function head is Matched; call 14 enters
`Functor.comp`/`Functor.comp` as application argument 2 (M1). Calls 15-16
descend through argument 7 of successive `Functor.comp` pairs (M2 after
exposure); call 18 compares `DerivedCategory.Plus`/`DerivedCategory`
as application argument 0 (M1), and call 20 compares
`Functor`/`Functor` through a structure field (M1). The raw M1 children
retain their parent's divergence hashes. This is the observed first
projection/application continuation toward the named argument-2 paths.

The argument-2 path then traverses a proposition-type comparison and
dependent binder body before its `argument[2]` and `argument[0]` siblings.
`is_def_eq_proof_irrel` creates the proposition-type child at
`type_checker.cpp:1652-1668`; `is_def_eq_binding` instantiates and compares
the body at `:1479-1535`; application congruence compares later arguments
at `:1628-1645` (`M1P-KERNEL.md`). The highest named argument-3 path starts
from the other `Functor.comp` endpoint and uses the same application and
dependent-body branches. Its first exact pair is beyond the 1,483-call
raw window, and the globally largest `__other__` bucket has no recoverable
single path. READY4.1 therefore cannot support a hand reconstruction of
the true highest-cost individual paths or their inclusive subtree times.
