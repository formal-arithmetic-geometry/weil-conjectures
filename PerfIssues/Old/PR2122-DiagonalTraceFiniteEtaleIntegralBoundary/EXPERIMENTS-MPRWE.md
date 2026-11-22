# Mismatch Provenance and Recursive Workload Report

Case: PR2122-DiagonalTraceFiniteEtaleIntegralBoundary
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; historical READY2
reference only. The fresh replay is unavailable because the read-only current
olean closure lacks `GmRelativeKummer.olean`.
Root: `Exists.casesOn` motive, witness, and final dependent body.

## 1. Root mismatch

The original recursor context is the root obligation. Extracting its final
branch changes the motive, so the exact left/right root terms cannot be
replayed or treated as a standalone matched pair.

## 2. Matched baseline

`MatchedGeneric` is **A3 diagnostic** only: a same-family proof body under
`Exists.casesOn`, compared with an `id`-wrapped body. Earlier READY2 measured
0.038 ms, two calls, depth 1, with one proposition comparison. It is not the
original recursor telescope.

## 3. Provenance distribution

Historical O trace: 2,227,198 calls, 11,486 ms comparison-exclusive and
14,349 ms reduction-exclusive, depth 93; 1,535,674 distinct and 691,524
repeated pairs. These are earlier-phase values. No fresh root is claimed.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | not separately measurable | not measurable | Unclassified |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | historical root only | 11,486 ms historical total | 100% of attributable trace |

## 4. Newly exposed divergences

No causal M2 event can be reconstructed without the missing source dependency
and the original `Exists.casesOn` context.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | No fresh replay. Historical O was 25,836 ms / 2,227,198 calls. |
| O1/O2/O12/O-all | Unavailable: branch extraction changes the recursor motive and is invalid. |
| R | Historical restored source exists, but no fresh compatible measurement is claimed. |

Historical broad A was 5.142 s / 510,125 calls, but it changes construction and
does not preserve M0.

## 6. Conclusion

This case is Outcome **E** (insufficient provenance), blocked by the missing
`GmRelativeKummer.olean` dependency and invalid standalone branch controls.
The restored source snapshot is retained as a historical artifact only; no
fresh R timing is claimed.

## MPRWE round 2

The dependency is present in the current olean tree. Fresh READY3.1 counter
and trace runs completed with the exact `Before.lean`/`OriginalRecursor`
source. The selected root had 2,227,198 calls, depth 93, and 13,821.715 ms
aggregate comparison-exclusive time; aggregate records partition the complete
root and the raw cap was consumed by earlier roots.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.041 | 0.000% |
| M1 | 1,749,276 | 13,669.989 | 98.901% |
| M2 | 12,631 | 121.003 | 0.876% |
| Matched | 464,966 | 27.748 | 0.201% |
| Unclassified | 324 | 2.933 | 0.021% |

The dominant M2 path is the nested `argument[6]/argument[0]/argument[0]`
branch (118.381 ms, including 12,529 calls); matched descendants on the same
branch are only 1.740 ms. The other top matched groups are proposition-type
paths in the recursor telescope. The root is therefore inherited M1 work with
a small, measurable M2 contribution.

The recursor branch extraction changes the motive and is invalid for C; no
descendant-only M2 alignment type-checks under the original recursor. The
restored source remains a historical artifact with no fresh R timing. Outcome:
**C** (M1 dominates; M2 is below 1%).

## MPRWE round 3 (READY3.2)

Shares are M1 98.901%, M2 0.876%, Matched 0.201%, Unclassified 0.021%.
The recursor branch extraction remains root-changing and invalid for C.
