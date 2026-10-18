## What changed

Repaired the returned delivery by removing the private theorem
`setChart_isPullback`. Its statement was identical to the existing
`AlgebraicGeometry.Etale.isPullback_pullbackFst_of_hom` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero`. The module now imports
that upstream module and calls the existing theorem at the chart-pasting step. The two
public base-change declarations and their proofs are otherwise unchanged. The existing
change record `coord/changes/N2-etale-set-flat-base-change-proof-scope.md` records the
proof-scope changes required by the delivery checks.

Validation: the module compiles cleanly with `lcompile.py` in 11.5 seconds. No new
statement, definition, axiom, or `sorry` was added.

## Proved and sorry left

Both original declarations remain proved:

- `AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_flat`.
- `AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_smooth`.

Remaining holes in this module: 0. Holes added: 0.

## No longer needed

- The duplicate private theorem `setChart_isPullback` and its proof are removed.
- Its local proof is replaced by `Etale.isPullback_pullbackFst_of_hom`.
- No dependency node or new module was needed; all other imports and proof dependencies
  remain in use.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated a theorem already present word-for-word in the
library, which the import-prune check correctly rejected. The existing theorem has the
same binders and conclusion, so the repair uses it directly.

## New nodes

None.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
