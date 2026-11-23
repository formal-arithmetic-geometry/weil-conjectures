# RealPurity M1 propagation (READY4.2)

The three fresh O repeats use `RealPurity/probes/mprwe/Original.lean` from
the reserved `m1p` import tree (revision `105ac3f5b23`). This fixes the
missing-import problem in the READY4.1 `n5` setup. READY4.2 revision is
`0311a15b5f4`.

| Repeat result | Value |
|---|---:|
| O counters / analyzed calls | 17,310,168 / 17,310,168 (all repeats) |
| Raw entered calls | 3,222 (0.019%) per repeat |
| M1 calls / call share | 7,988,264 / 46.148% |
| M1 time share | 62.315% [62.170--64.097%] |
| M2 / Matched median time shares | 36.409% / 1.273% |

The root count is 30,068 below the RealPushforward READY4.1 `n5` run;
RealPurity did not run under READY4.1. This required `m1p` import closure
is a different, fully built revision; no other root's count is substituted.
All aggregate labels and transitions cover the analyzed root.

## A2/A3

M1 depth mean/median/p90/p99/max is 85.865/86/88/90/91. The 50% and 90%
bands are 84--86 and 79--89. Fan-out mean/median/p90/max is 1.274/1/1/18.
The analyzer verdict is **deep**. M1 edges are M1->M1 6,491,456,
M1->Matched 1,695,794, and M1->M2 1,987,467.

The displayed rows cover 93.0% of M1 exclusive time. Parent=M2 rows are
shown because they feed M1 children in this mixed root; the parent=M1 rows
are the M1-parent subset.

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M1 | M1 | projection / projection | 4,287,141 | 19,392.788 | 1.000 |
| M2 | M1 | quick / dependent-body | 956,028 | 17,829.550 | 1.000 |
| M1 | M1 | quick / dependent-body | 501,080 | 12,364.254 | 1.000 |
| M2 | M1 | application / argument | 539,634 | 7,713.810 | 8.802 |
| M1 | M1 | application / argument | 274,124 | 5,666.211 | 9.227 |

Projection to projection is the dominant M1 transition, matching EtaleHom;
the same strategy remains dominant with a large M2 subtree. C was not
requested for this control.
