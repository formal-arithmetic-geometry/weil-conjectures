# OrderedSpectralRawLattices M1 propagation (READY4.2)

The three fresh O repeats use `OrderedSpectralRawLattices/probes/mprwe/Original.lean` from `m1p` revision `105ac3f5b23`, with READY4.2 (`0311a15b5f4`). Root 62844 reaches the expected deterministic timeout after the aggregate root is complete.

| Repeat result | Value |
|---|---:|
| O counters / analyzed calls | 18,944,709 / 18,944,709 (all repeats) |
| Raw entered calls | 4,333 (0.023%) per repeat |
| M1 calls / call share | 8,320,909 / 43.922% |
| M1 time share | 64.684% [62.351--64.750%] |
| M2 / Matched median time shares | 34.531% / 0.784% |

Call counts are deterministic. The root and label counts match READY4.1; the
time spread is the expected mixed timeout-path noise. Aggregate coverage is
complete despite the bounded raw stream.

## A2/A3

M1 depth mean/median/p90/p99/max is 63.572/64/68/70/71. The 50% and 90%
bands are 60--65 and 57--69. Fan-out mean/median/p90/max is 1.754/1/8/18.
The analyzer verdict is **wide**. M1 edges are M1->M1 5,076,832,
M1->Matched 6,741,771, and M1->M2 2,780,258.

Rows below cover 91.7% of M1 exclusive time; parent=M2 rows are included to
show the M1 work exposed by the large M2 branch.

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M2 | M1 | quick / dependent-body | 485,139 | 16,740.018 | 1.996 |
| M1 | M1 | application / argument | 1,792,309 | 15,101.023 | 6.738 |
| M1 | M1 | projection / projection | 2,900,427 | 13,691.386 | 1.000 |
| M2 | M1 | application / argument | 1,073,171 | 5,237.753 | 8.803 |

The dominant M1-only transition is application to argument, unlike the
projection-dominant primary roots. The same application strategy remains
visible while M2 is large. C was not requested for this control.
