## What changed

Completed `WeilConjectures.sequenceDerivedScalarUnit` in
`Sheaf.Paper.SequenceDerivedScalarUnit`, preserving its entire signature and
public import. Added private proof imports for the existing whole-system
comparison API, ordinary scalar-unit interchange, and K-flat resolutions.

Two proved private helpers reduce natural-transformation equality to flat-term
K-flat representatives and convert the existing residue-field invertibility
hypotheses to the stalk-unit hypotheses of ordinary interchange. The proof uses
the canonical scalar-unit and scalar/pullback normalization equations, ordinary
interchange degree by degree, and naturality of the exact-pullback factorization.
The equation holds for arbitrary unbounded inputs and independent coefficient
and scheme universes. Updated the item's DAG proof to record this direct route.

Validation: the completed module compiled cleanly through `lcompile.py` in
9.1 seconds, with no errors or warnings. The public theorem signature is
textually unchanged, and every Lean line is at most 100 characters.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.sequenceDerivedScalarUnit`
(node `lem-trf-sequence-derived-scalar-unit`).

No holes remain in this module. Added zero holes and zero split-off statements.
This is a proof from existing declarations, including the separately assigned
ordinary theorem `WeilConjectures.sequenceScalarUnit_interchange`; its existing
hole is not claimed as closed by this delivery.

## No longer needed

Removed the item's proof dependency on
`lem-trf-ringed-kflat-word-comparison-descent`
(`Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`). Its general finite-word
descent machinery is unnecessary for this component: localization extensionality,
one K-flat resolution, and the prescribed comparison formulas suffice. No Lean
module or declaration is withdrawn. No original public import was removed.
The ordinary scalar-generator dependency remains necessary. The existing
comparison definitions may retain transitive dependencies of their own.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The original proof plan was
correct but cited general word descent where a direct component calculation
suffices. Its flat-term assumption is required only of a chosen resolution,
never of the input to the theorem. The current source exists despite the older
quarantine row in `coord/rework.tsv`; this delivery preserves its declaration
and attachment.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
