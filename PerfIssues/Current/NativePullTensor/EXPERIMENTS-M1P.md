# READY4 M1 propagation: NativePullTensor

## Validation

The Lean 4.35.0 READY4 binary was run from the read-only NativePullTensor
workspace with the exact current probe and the accepted root operation. The
selected process-wide root was `18506`. Counter and trace instrumentation
agree on 2,685,580 recursive calls and a successful result.

| label | calls | exclusive ms | time share |
|---|---:|---:|---:|
| M0 | 1 | 0.015 | 0.000% |
| M1 | 1,120,689 | 21,733.131 | 98.051% |
| M2 | 12,041 | 72.251 | 0.326% |
| Matched | 1,552,849 | 359.739 | 1.623% |
| Unclassified | 0 | 0.000 | 0.000% |
| **root** | **2,685,580** | **22,165.136** | **100%** |

READY3.2 accepted shares were M1 98.126%, M2 0.302%, Matched 1.569%.
The call total is identical. The small share movement is from READY4's
additional branch bookkeeping and the selected exact root's timing; it does
not indicate a semantic change. All READY4 calls receive a complete
provenance label; raw event capture is bounded and is not used for shares.

## Transition summary

The complete matrix contains 2,685,579 child edges and 22,165.121 ms edge
exclusive time, plus 0.015 ms root direct time. The largest rows are:

| parent | child kind | calls | exclusive ms | reduction ms |
|---|---|---:|---:|---:|
| application | function-head | 189,446 | 6,702.805 | 697.020 |
| application | argument | 693,554 | 6,407.333 | 3,673.777 |
| lazy_delta | argument | 887,573 | 3,146.107 | 2,728.620 |
| projection | projection | 59,456 | 1,908.852 | 472.447 |
| projection | argument | 728,114 | 1,701.142 | 60.139 |
| second_whnf | fallback | 63,094 | 1,065.864 | 456.873 |
| proof_irrelevance | proposition-type | 32,060 | 632.843 | 22.779 |
| quick | dependent-body | 32,195 | 598.748 | 783.936 |

M1 depth reaches bucket 65 (mean 43.489) and fan-out bucket 28 (mean
2.375), so this root is both deep and wide. M2 reaches depth bucket 65 and
fan-out bucket 8. Matched nodes have no propagated children in the
provenance projection. No transition has an unknown branch above 5% of root
time; failure-followup counts are zero in the selected rows.

## Raw capture and overhead

The selected root's aggregate coverage is complete (2,685,580/2,685,580).
The detailed event file contains other process roots and is bounded by the
configured raw-event cap; the selected root did not rely on raw enter/exit
records for classification. READY4 root wall measurements were 28.212 s in
counters mode and 31.063 s in trace mode. The existing READY3.2 paired
Native controls report 16.554 s counter comparison-exclusive and 20.949 s
trace comparison-exclusive for the accepted root. These are paired
observations rather than a normalized overhead percentage because the
instrumentation schema and source/build setup differ; no semantic path was
changed.
