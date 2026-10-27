## What changed

Proved `WeilConjectures.sequenceDerivedMixed` in
`Sheaf.Paper.SequenceDerivedMixedSquare` without changing its statement or definitions.
The proof uses a flat-term K-flat resolution of the whole sequence complex, the existing
scalar-comparison normalization equations, the exact geometric comparison equations, and
`sequenceScalarGeometric_interchange_cochain`. It compares the two routes after the common
invertible target counit, then extends equality by naturality and localization.

Added proof imports for the sequence-system private preservation theorem, ordinary
interchange, and K-flat resolution. Added proved private helpers for exact compositor
normalization, categorical pasting of normalized squares, and the
residue-field-to-stalk unit implication. Updated the item's DAG proof
to this calculation. No other existing modules or nodes are changed.

Validation: the delivered Lean module compiled through `lcompile.py` in 27.3 seconds,
with no errors or warnings. Its theorem signature is unchanged.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.sequenceDerivedMixed`
(node `lem-trf-sequence-derived-mixed-square`). Added 0 holes and split off 0 statements.
There are no remaining `sorry` declarations in the delivered module. The proof uses the
existing ordinary interchange statement; its separate proof obligation is unchanged.

## No longer needed

No existing import was removed. This proof does not use
`lem-trf-ringed-kflat-word-comparison-descent` or import
`Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`: constructing its general word
and edge packages is unnecessary for this single square. The common resolution and
normalization calculation are applied directly. Its existing declarations remain available
for other consumers. No module is withdrawn. All other declared dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the item. The planned generic finite-word descent
step can be replaced by the direct counit calculation. The rework archive is not withdrawn;
the current restored source and its statement were preserved.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
