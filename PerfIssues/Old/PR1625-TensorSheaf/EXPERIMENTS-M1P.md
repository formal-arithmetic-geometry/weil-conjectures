# PR1625: M1 propagation (READY4.1)

## Original root and validity

The original `OriginalNestedApp.lean` probe ran under READY4.1 Lean 4.35.0
with a 3600 s limit. Process-wide root 65966 is a Pi/Pi comparison (raw
head code `7`/`7`) whose binder-body argument 15 enters the dependent
`Eq`/`Eq` obligation for the nested `.app` path. The first structural
divergence is in that body at
`root/body/body/body/body/body/body/body/body/body/body/body/body/body/body/body/fn/fn/arg/fn/arg/fn/fn/fn/fn/fn/arg/fn/fn/fn/fn`.
The root completed with 11,757,788 calls, 74,220.872 ms comparison-exclusive
time, and 120,984.895 ms root wall. A separate fresh counters run measured
11,757,788 calls, 89,697.874 ms root wall, and 49,224.515 ms
comparison-exclusive time. The call count equals the accepted READY3.2 count; this run's M1
share differs from its 99.406% by 0.031 percentage points.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.636 | 0.001% |
| M1 | 8,111,028 | 73,803.268 | 99.437% |
| M2 | 4,686 | 54.054 | 0.073% |
| Matched | 3,642,041 | 362.111 | 0.488% |
| Unclassified | 32 | 0.803 | 0.001% |

Analyzer revision: READY4.1 `mprwe_analyze.py`, kernel dataset commit
`5ae674db0c7`. Aggregate coverage is 11,757,788/11,757,788 calls; raw
capture is 1,703 entered and 1,613 exited calls (0.0145% by entered
calls). The aggregate labels, depth histograms, and transition totals cover
all calls independently of bounded raw capture. The 11,757,787 child edges
and 0.636 ms root direct time sum to the root exclusive total. Depth calls,
exclusive time, and reduction time reconcile with every label total; no
depth was clamped.

## A2: topology

M1 depth: mean 100.093, median 101, p90 112, p99 119, max 125. The
narrowest bands holding 50% and 90% of M1 exclusive time are depths
94-106 and 85-115. M1 depth histogram, binned by tens (start: calls /
exclusive ms): 0:43/0.8; 10:153/2.3; 20:715/7.1; 30:5,136/48.3;
40:21,884/177.3; 50:40,090/321.5; 60:49,402/447.4;
70:168,669/1,944.4; 80:779,765/7,581.9; 90:2,350,523/22,705.3;
100:3,327,506/29,500.8; 110:1,319,578/10,893.5; 120:47,564/172.8.

M1-parent fan-out across all child labels: mean 1.448, median 1, p90 3,
max 28. Exact histogram (children:nodes): 0:2,850,417; 1:2,600,305;
2:1,033,469; 3:851,772; 4:337,615; 5:13,947; 6:204,488;
7:71,565; 8:3,910; 9:110,755; 10:24,313; 11:2,053; 12:3,672;
13:2,248; 15:337; 28:162. Bounded raw capture observes 649
M1-to-M1, 1,024 M1-to-Matched, and 9 M1-to-M2 edges. Complete
label-to-label edge totals are not emitted by the unchanged READY4.1 patch;
the raw counts are sample observations only.

This is **mixed** propagation: a long dependent-body chain reaches depth
125, and application and projection descent creates side branches at the
expensive depths. The two highest named path buckets alone contain
8,071,710 M1 calls.

## A3: branch transition matrix

These complete rows cover all child labels. The first five hold
68,626.260 ms (92.46% of root exclusive time), bounding more than 90% of
M1 work even if all non-M1 time fell in them. READY4.1 does not provide
mean fan-out by parent branch; the full M1-parent mean is above.

| Parent branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 1,697,621 | 28,088.792 |
| application | argument | 5,377,086 | 24,799.684 |
| application | function-head | 2,349,001 | 7,634.986 |
| second_whnf | fallback | 562,881 | 5,462.712 |
| quick | dependent-body | 220,514 | 2,640.086 |
| lazy_delta | argument | 960,483 | 2,033.773 |
| proof_irrelevance | proposition-type | 155,955 | 1,723.478 |
| projection | argument | 321,427 | 1,539.040 |
| remaining rows | mixed | 112,819 | 297.685 |

The top M1 aggregate bucket is
`root/binder_body[15]/argument[1]/argument[0]/argument[6]/argument[0]/*`
(8,022,072 calls; 73,113.766 ms). The next named buckets are
`root/binder_body[15]/argument[2]/argument[0]/argument[7]/argument[0]/*`
(49,638; 385.363 ms) and
`root/binder_body[15]/argument[2]/function/projection/argument[0]/*`
(39,240; 302.626 ms). `*` groups deeper paths; none is a single known
subtree with a measured inclusive time.

## A4: first transitions of the costly paths

The M0 Pi/Pi pair enters `Eq`/`Eq` at call 2 via `dependent-body[15]`;
call 4 compares `Quiver.Hom`/`Quiver.Hom` as application argument 0.
The dominant sibling starts at call 44, where `Eq`/`Eq` compares
`CategoryStruct.comp`/`CategoryStruct.comp` as argument 1. Calls 45-49
continue through `DFunLike.coe`, `EquivLike.coe`, `Equiv.toFun`,
`Equiv.proj`, and `equivShrink`; the last step is projection descent.
Call 53 then compares a `CategoryStruct.comp` argument 0 pair; call 55
compares `DFunLike.coe`/`DFunLike.coe` as argument 7, leading into the
nested application chain represented by the large `argument[6]` bucket.
Each listed M1 child retains its parent's divergence hashes in the raw
trace, so these are continuations of the original mismatch lineage.

The two `argument[2]` cost buckets share the first binder-body transition
but branch at the later application argument. Their exact deep pairs are
outside the 1,703-call raw window; only their aggregate branch path and
cost are retained. In the exact Lean 4.35.0 kernel, `is_def_eq_binding`
instantiates and compares dependent bodies at `type_checker.cpp:1479-1535`,
`is_def_eq_app` compares function then arguments at `:1628-1645`, and
`lazy_delta_proj_reduction` re-enters projected components at `:1857-1880`
(`M1P-KERNEL.md`). The raw window cannot establish an inclusive time or
maximum fan-out for each named bucket.

## C: M0-preserving cut point

The highest-cost candidate is the nested argument-6 major premise. The
available alignment replaces that outer major premise, which instantiates
the dependent result type and changes the root Pi/body conversion; it
removes M0. A replacement restricted to the descendant must inhabit the
original instantiated domain, while the aligned proof inhabits the changed
domain. No type-correct local replacement preserving the same telescope
was constructed. O-cut therefore has no valid measurement, and no causal
speedup is claimed. The restored snapshot is byte-identical to O but is not
a selective restoration control.
