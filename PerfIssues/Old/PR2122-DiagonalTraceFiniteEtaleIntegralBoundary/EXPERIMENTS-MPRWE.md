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
