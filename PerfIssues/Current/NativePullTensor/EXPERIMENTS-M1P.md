# READY4.1 M1 propagation: NativePullTensor

## Validation

The Lean 4.35.0 READY4.1 binary was run from the read-only NativePullTensor
workspace with the exact current probe and the accepted root operation. The
selected process-wide root was `18506`. Counter and trace instrumentation
agree on 2,685,580 recursive calls and a successful result.

| label | calls | exclusive ms | time share |
|---|---:|---:|---:|
| M0 | 1 | 0.012 | 0.000% |
| M1 | 1,120,689 | 21,106.863 | 98.085% |
| M2 | 12,041 | 69.554 | 0.323% |
| Matched | 1,552,849 | 342.570 | 1.592% |
| Unclassified | 0 | 0.000 | 0.000% |
| **root** | **2,685,580** | **21,519.000** | **100%** |

READY3.2 accepted shares were M1 98.126%, M2 0.302%, Matched 1.569%.
The call total is identical. Relative to READY4, all label shares moved by
less than 0.1 percentage point. All READY4.1 calls receive a complete
provenance label; raw event capture is bounded and is not used for shares.

## Transition summary

The complete matrix contains 2,685,579 child edges and 21,518.988 ms edge
exclusive time, plus 0.012 ms root direct time. The largest rows are:

| parent | child kind | calls | exclusive ms | reduction ms |
|---|---|---:|---:|---:|
| application | function-head | 189,446 | 6,604.879 | 666.433 |
| application | argument | 693,554 | 6,163.627 | 3,537.574 |
| lazy_delta | argument | 887,573 | 3,045.356 | 2,599.763 |
| projection | projection | 59,456 | 1,842.577 | 436.439 |
| projection | argument | 728,114 | 1,647.878 | 53.849 |
| second_whnf | fallback | 63,094 | 1,018.079 | 412.879 |
| proof_irrelevance | proposition-type | 32,060 | 613.416 | 21.673 |
| quick | dependent-body | 32,195 | 581.775 | 753.366 |

M1 exact depth has mean 43.511, median 44, p90 55, p99 65, and maximum
81. The narrowest contiguous depth bands containing 50% and 90% of M1
exclusive time are 36--47 and 26--56. M1 fan-out has mean 2.375, median 0,
p90 9, and maximum 28. M2 depth has mean 45.416, median 45, p90 58,
p99 67, and maximum 76; Matched depth has mean 43.277, median 44, p90
55, p99 65, and maximum 81. No calls were clamped above depth 4096.
Every label's depth calls and exclusive/reduction time sum to its label
totals. The root is both deep and wide. Matched nodes have no propagated
children in the provenance projection. No transition has an unknown branch
above 5% of root time; failure-followup counts are zero in the selected rows.

## Raw capture and overhead

The selected root's aggregate coverage is complete (2,685,580/2,685,580).
The detailed event file contains other process roots and is bounded by the
configured raw-event cap; the selected root did not rely on raw enter/exit
records for classification. READY4 counters root wall time was 28.212 s;
the fresh READY4.1 trace root wall time was 30.003 s. The existing READY3.2 paired
Native controls report 16.554 s counter comparison-exclusive and 20.949 s
trace comparison-exclusive for the accepted root. These are paired
observations rather than a normalized overhead percentage because the
instrumentation schema and source/build setup differ; no semantic path was
changed. A fresh no-instrumentation 4.35 binary run of the same probe
completed successfully in 262.87 s process wall, but it emits no recursive
call counter and its root span cannot be matched to the READY4 root. It is
recorded as a baseline observation, not divided into an overhead percentage.

## P: fresh original and C cut-point assessment

This section uses a new READY4.1 Lean 4.35.0 run of the original
`OriginalRoot.lean` probe with a 3600 s limit; the A2-A4 measurements above
are K's earlier independent run. The new selected process-wide root is
18506: 2,685,580 aggregate calls, 24,978.860 ms comparison-exclusive
time, and 38,189.966 ms root wall. M1 has 1,120,689 calls and
24,553.873 ms (98.299%); M2 has 12,041 and 73.550 ms; Matched has
1,552,849 and 351.389 ms; M0 has one call and 0.047 ms.
The new M1 share is 0.173 percentage points above the accepted READY3.2
share, within the 0.5-point consistency bound. Aggregate coverage is
2,685,580/2,685,580 calls; raw capture is 1,723 entered and 1,665 exited
calls. Analyzer revision: READY4.1 `mprwe_analyze.py` at kernel dataset
commit `5ae674db0c7`. A separate fresh counters run measured 2,685,580
calls, 23,330.541 ms root wall, and 16,177.468 ms comparison-exclusive
time. Its count agrees with the new analyzed root.

The candidate cut points are the two expensive `Exists.choose` domain
continuations in the original root, notably the M1 aggregate buckets at
`root/binder_domain[0]/argument[2]/argument[6]/argument[7]/binder_body[5]/*`
(305,588 calls; 7,481.056 ms) and
`root/binder_domain[0]/argument[3]/argument[7]/argument[7]/binder_body[5]/*`
(305,588 calls; 6,449.416 ms). In the original source,
`nativePullTotalTensor` is `(exists_nativePullTotalTensor ...).choose`
and is passed to `nativeRestrictionDerivedTensor` when forming
`nativePullTensor`. Changing that provider changes the dependent argument
and hence the root's inferred/expected type pair. The existing aligned
diagnostic replaces that provider/root rather than one child at the same
required type. A child proof under the aligned provider inhabits its new
dependent domain, not the original domain. No type-correct source-level
replacement of either selected child preserving M0 and the same telescope
was constructed. O-cut has no valid run, and an O/O-cut/O-restore cost
comparison would be misleading. The restored source snapshot is freshly
verified byte-identical to O, but is not a selective restoration control.
