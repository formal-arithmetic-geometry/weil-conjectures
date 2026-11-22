# Mismatch Provenance and Recursive Workload Report

Case: PR1624-IntegersSheafHomologyTower
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; earlier IM/AD
measurements with READY2-4.35.0.
Root: complete dependent `Iso.trans` endpoint, with two `Functor.comp`
descendants.

## 1. Root mismatch

The endpoint `Functor.comp` arguments 2 and 3 are the first recorded
representation divergence. The original dependent endpoint consumer is retained
only in O/R snapshots; exact terms are not serialized by READY2.

## 2. Matched baseline

`MatchedDiagnostic`/`MatchedGeneric` are **A3 diagnostic** controls. The exact
old endpoint consumer could not be replayed with the available olean closure;
the same-family `Functor.comp` pair is non-structural and measured 0.050 ms,
one call, depth 0 (earlier IM round 2). It is not evidence for an A0 root.

## 3. Provenance distribution

Earlier O trace root: 6,598,545 calls, 37,377.645 ms comparison-exclusive,
29,061.999 ms reduction-exclusive, depth 88; 3,361,091 distinct and 1,638,909
repeated pairs. READY2 lacks parent IDs and reduction links.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 6,598,544 recursive calls (inferred) | 37,377.645 ms measured total | 100% of attributable trace |

## 4. Newly exposed divergences

The two isolated endpoint checks were 17,942 and 30,066 ms (earlier IM), but
there is no parent-to-child trace proving whether they are M1, M2, or matched.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier root: 53,520.575 ms, 6,598,545 calls. |
| O1/O2/O12/O-all | Unavailable. The broad aligned endpoint changes the dependent endpoint and removes M0; no child-only source type-checks under the original telescope. |
| R | No separately measured restored endpoint was available in the existing AD/IM artifacts; the restored source snapshot is retained for a future compatible replay. |

The available aligned endpoint was 5.256 s / 456,393 calls, but it is an
invalid C control for this question.

## 6. Conclusion

The standalone matched diagnostic is cheap, while the dependent endpoint is
expensive and alignment removes most work. The endpoint context is a mixed
intrinsic/mismatch interaction, Outcome **D/E**; provenance is unclassified.
The restored source snapshot retains the original declaration context; no
separate restored endpoint timing was available.

## MPRWE round 2

## MPRWE round 4 (READY3.2; supersedes earlier tables)

The fresh O probe failed before the intended expensive root: the source
reported unknown free variable _fvar.17433 and “final iso argument did not
Kernel-check”. The only roots were small setup roots (285,192 and 285,229
calls), so no valid O root, analyzed shares, or C comparison is reported.
Analyzer READY3.2. Outcome: E (type-level source obstruction).

READY3.1-4.35.0 fresh counter and trace runs completed. The selected original
root had 6,598,545 calls, depth 88, and 40,848.850 ms aggregate
comparison-exclusive time. Aggregate records are complete; raw selected-root
coverage was 0 because earlier roots consumed the cap.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.022 | 0.000% |
| M1 | 5,215,138 | 40,770.605 | 99.809% |
| M2 | 287 | 2.587 | 0.006% |
| Matched | 1,383,111 | 75.410 | 0.185% |
| Unclassified | 8 | 0.227 | 0.001% |

The endpoint's large descendant groups are M1 continuations. The largest M2
groups are isolated endpoint/proposition paths (the largest single group is
0.645 ms); the corresponding matched paths are also small. This answers the
endpoint question: the residual work is inherited, not a newly exposed
mismatch cascade.

The broad aligned endpoint changes the dependent telescope and removes M0, so
it is invalid for C. No descendant-only M2 alignment type-checks under the
original endpoint. O and R snapshots are byte-identical; the earlier aligned
measurement was 5.256 s / 456,393 calls. Outcome: **C**.

## MPRWE round 3 (READY3.2)

Shares are M1 99.809%, M2 0.006%, Matched 0.185%, Unclassified 0.001%.
The endpoint alignment remains root-changing and invalid for C.
