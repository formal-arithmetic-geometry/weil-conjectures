## What changed

Proved `rhsCore` by composing two strictly smaller transport statements. Added
`rhsCoreBridgeCancellation` for cancellation of the canonical bridge coordinates and
`rhsCoreFiniteMate` for conversion of the resulting evaluated semilinear mate to the
fixed finite proper/open mate.

## Proved and sorry left

`rhsCore` is proved. The two strictly simpler intermediate declarations remain as
named stage-3 splits: `rhsCoreBridgeCancellation` and `rhsCoreFiniteMate`.

## No longer needed

No declared dependency was removed. The proof uses only the finite evaluation
coordinates, canonical bridge, ambient proper/open calculus, and the two new split
statements.

## Where the brief, the DAG or earlier work was wrong

The original node bundled bridge cancellation and finite mate conversion into one
statement. The proof separates these two genuinely distinct categorical calculations.

## New nodes

`lem-sf-system-finite-refinement-mate-rhs-normalization-bridge-cancellation` and
`lem-sf-system-finite-refinement-mate-rhs-normalization-finite-mate`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SystemFiniteRefinementMateRhsBridgeCancellation": "24dab1a6bf73a1977b7a0ec4e5fc528970f4dd21", "Sheaf.Paper.SystemFiniteRefinementMateRhsCore": "3775b3b45a6ed5083b0a133f1e6211f47226f0e1", "Sheaf.Paper.SystemFiniteRefinementMateRhsCoreFiniteMate": "f3ae8e0d81256f2ed258d1c6df71fc5fc38c5d31"}, "results": {}, "time": "2026-10-28T09:57:25+0800", "transitive": 0, "version": 1}
```

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
