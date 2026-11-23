# FiniteBaseChange M1 propagation (READY4.2)

The three fresh O repeats use `FiniteBaseChangeRestrictionMateTransport/probes/mprwe/Original.lean` from `m1p` revision `105ac3f5b23`, Lean 4.35.0, and READY4.2 (`0311a15b5f4`). Root 16563 is the dependent `hb` comparison.

| Repeat result | Value |
|---|---:|
| O counters / analyzed calls | 239,340,712 / 239,340,712 (all repeats) |
| Raw entered calls | 3,828 (0.002%) per repeat |
| M1 calls / call share | 130,197,227 / 54.398% |
| M1 time share | 72.869% [72.843--73.112%] |
| M2 / Matched median time shares | 25.661% / 1.419% |

The call counts and labels are deterministic across repeats. READY4.2
aggregate coverage is complete; the bounded raw stream is used only for
manual inspection. The root count matches READY4.1. The changed import tree
and READY4.2 branch accounting explain the timing difference from READY4.1.

## A2/A3

M1 depth mean/median/p90/p99/max is 74.992/75/79/80/87. The 50% and 90%
bands are 71--74 and 68--78. Fan-out mean/median/p90/max is 1.081/1/1/21.
The analyzer verdict is **deep**. M1 edges are M1->M1 89,755,076,
M1->Matched 23,447,508, and M1->M2 27,479,827.

For mixed roots, the rows below include every parent label feeding an M1
child so that the displayed rows cover 91.3% of M1 exclusive time. The
parent=M1 subset is the actual M1-parent matrix; parent=M2 rows are included
because they carry a large fraction of M1 time in this mixed workload.

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M1 | M1 | projection / projection | 59,274,323 | 257,589.129 | 1.000 |
| M2 | M1 | quick / dependent-body | 13,217,806 | 179,588.864 | 1.000 |
| M1 | M1 | quick / dependent-body | 6,928,195 | 115,951.384 | 1.000 |
| M2 | M1 | application / argument | 7,461,937 | 73,623.315 | 8.802 |
| M1 | M1 | application / function-head | 19,747,308 | 55,885.726 | 1.000 |

The dominant M1 transition is M1 projection to projection. It matches the
EtaleHom strategy even though M2 remains large; the quick dependent-body
continuation is the main mixed-case secondary path.

## C

The step-2 `hb` descendant-alignment candidate remains a no-op at the
original root: it preserves the workload rather than cutting the selected
M1 subtree. The whole-`hb` transport changes M0. The new matrix adds no
type-correct M0-preserving cut-point, so no new intervention was claimed.
