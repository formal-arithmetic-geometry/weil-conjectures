# PR1627 control: M1 propagation (READY4.1)

The original `OriginalGeneratedFields.lean` probe ran under READY4.1
Lean 4.35.0 with a 3600 s limit. A separate fresh counters run measured
10,904,899 calls at process-wide root 15228, 34,738.697 ms root wall,
and 18,965.758 ms comparison-exclusive time. The selected repeat trace
has the same 10,904,899 calls, 44,722.581 ms root wall, and
28,701.265 ms comparison-exclusive time. Its root is the generated
dependent Pi/body comparison; the raw first transitions enter an `Eq`/`Eq`
body and then the `ObjectProperty.homMk`/`CategoryStruct.comp` pair.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.041 | <0.001% |
| M1 | 2,619,482 | 18,229.049 | 63.513% |
| M2 | 1,512,663 | 7,940.465 | 27.666% |
| Matched | 6,772,753 | 2,531.710 | 8.821% |
| Unclassified | 0 | 0 | 0% |

Analyzer revision: READY4.1 `mprwe_analyze.py`, kernel dataset commit
`5ae674db0c7`. Aggregate coverage is 10,904,899/10,904,899 calls.
Raw capture is 1,518 entered and 1,479 exited calls (0.0139% by entered
calls). The 10,904,898 child edges plus 0.041 ms root direct time
reconcile to the root total. Per-label depth calls and exclusive/reduction
times match aggregates; no depth was clamped.

The accepted READY3.2 label call counts are identical to this run's counts,
but its M1/M2/Matched time shares were 66.712/22.789/10.495%; the
READY4.1 repeat differs by -3.199/+4.877/-1.674 percentage points.
A first fresh READY4.1 trace of the same root and identical label calls
measured 64.770/26.102/9.128% and 52,869.899 ms root wall. The repeat's
root wall is 8,147.318 ms shorter, and its M1 share moves another 1.257
points despite unchanged calls, label assignment, and transition counts.
The instrumentation uses `std::chrono::steady_clock` wall time
(`type_checker.cpp:39`), which includes scheduling and tracing overhead.
Thus the root selection and provenance are reproducible, while the
exclusive-time partition is not stable to 0.5 points under these runs.
The shares in this report are measured, with that limit on precision;
the discrepancy is a timing effect rather than a different root.

## A2: depth and fan-out

M1 depth mean 33.464, median 34, p90 37, p99 50, max 61. The narrowest
bands containing 50% and 90% of M1 exclusive time are depths 29-35 and
24-37. Ten-depth histogram (start: calls/exclusive ms): 0:14/0.9;
10:2,671/70.7; 20:430,710/6,020.4; 30:2,052,035/11,355.1;
40:106,787/645.7; 50:26,806/135.3; 60:459/0.9.

M1-parent fan-out over all child labels: mean 2.037, median 0, p90 9,
max 18. Exact histogram (children:nodes): 0:1,445,221;
1:533,190; 2:3,139; 3:1,239; 4:112,223; 5:110,977;
6:37,005; 7:1,167; 8:85; 9:332,996; 10:139; 11:7;
12:40; 13:35,758; 14:3,746; 15:1,239; 17:72; 18:1,239.
The bounded raw window observes 179 M1-to-M1, 401 M1-to-Matched,
and 203 M1-to-M2 edges. Complete label-to-label edge counts are not
emitted by the unchanged patch; the raw counts are only sample observations.

This case is **wide** relative to the other PerfIssues roots: median depth
34 and 90% of M1 time within depths 24-37, but a 9-child p90 fan-out and
many 9- or 13-child M1 parents. The high fan-out repeatedly exposes M1,
M2, and cheap Matched side comparisons.

## A3: transition matrix and Matched work

Rows cover all child labels. The top five contain 28,019.401 ms,
97.624% of root exclusive time. Even subtracting all non-M1 time, they
contain at least 96.259% of M1 exclusive time. READY4.1 does not emit
mean fan-out by branch; the complete M1-parent mean is above.

| Parent outcome | Child kind | Calls | Exclusive ms | Failure follow-up calls |
|---|---|---:|---:|---:|
| failure | argument | 6,671,717 | 11,354.811 | 2,480 |
| failure | fallback | 1,331,712 | 6,576.363 | 998,784 |
| quick | dependent-body | 371,583 | 5,075.001 | 0 |
| quick_reduced | dependent-body | 185,806 | 3,597.830 | 0 |
| failure | field | 287,788 | 1,415.396 | 106,897 |
| remaining rows | mixed | 2,056,292 | 681.823 | mixed |

`failure` is the *parent's final comparison outcome*, not a separate
kernel branch that initiates all those children. Its argument/field
children are created during application or structure comparison; many
failed children are followed by fallback work. This follows the exact
`is_def_eq_core` sequence at `type_checker.cpp:1909-1990` and the
instrumentation's parent-outcome recording (`M1P-KERNEL.md`).

Matched calls are 6,772,753 (62.107% of calls) but only 8.821% of
exclusive time. Their five largest aggregate buckets occupy the same
generated-field `binder_body[2]/argument[2]/argument[6]/argument[5]`
argument-8 through argument-12 paths as the five largest M1 buckets.
For example, the argument-12 bucket has 632,683 M1 calls and
4,576.601 ms, alongside 1,630,679 Matched calls and 605.510 ms.
This connects the previously noted substantial Matched work to the
M1-bearing dependent branch: repeated sibling comparisons can be
structurally matched while the inherited mismatch path remains costly.
The bounded raw M1-to-Matched edges support local adjacency, but the
aggregate rows cannot prove a complete parent-child split by label.
