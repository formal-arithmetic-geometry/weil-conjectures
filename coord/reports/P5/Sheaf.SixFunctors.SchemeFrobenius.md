## What changed

Filled the proof of `WeilConjectures.FiniteFieldDatum.schemeFrobenius_isFinite_isRadicial` in `lean/Sheaf/SixFunctors/SchemeFrobenius.lean`. The proof applies the existing
`WeilConjectures.FiniteFieldDatum.relativeFrobenius_isFinite_isRadicial` theorem; the two morphisms are definitionally the same because `schemeFrobenius` is defined as `relativeFrobenius`. No imports, declarations, signatures, definitions, or DAG statements were changed.

## Proved and sorry left

Closed the only theorem hole, `WeilConjectures.FiniteFieldDatum.schemeFrobenius_isFinite_isRadicial` (1 of 1). No `sorry` remains in the delivered module.

## No longer needed

None. The module's existing public imports are needed by its declarations and definitions; the proof uses `Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial`.

## Where the brief, the DAG or earlier work was wrong

None found.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
