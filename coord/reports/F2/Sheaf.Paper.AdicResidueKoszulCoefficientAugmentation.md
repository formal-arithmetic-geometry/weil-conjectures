## What changed

Proved `AlgebraicGeometry.Scheme.adicResidue_koszul_coefficient_augmentation`
without changing its statement, public imports, or the existing tensor-augmentation
constructions. The proof constructs the actual coefficient quotient map from the
unit section, proves scalar-power annihilation using the completion projections,
and builds the chain maps using negative Koszul duality. Normalization determines
the successor squares because the degree-zero dual unit is invertible.

Added the proved module `Sheaf.CategoryTheory.RingedNegativeKoszulLowDegrees`.
It identifies the two highest terms of the actual negative complex, including
its canonical empty-subset basis and its last differential. Its proof specializes
`exists_ringedSignedKoszulFiniteCoordinates` to the regular module in degree zero,
discards the zero summands, and checks the tensor unitors and singleton matrix
entries. Both new proof imports in the item are private imports. Updated the
item's DAG proof to describe this argument and added the new lemma's node.

Validation: both delivered modules compiled cleanly through `lcompile.py --all`.
Profiling identified an expensive successor-map rewrite; the proof now uses its
explicit equality by composition and cancels the explicit degree-zero isomorphism.
No profiling or tracing options remain.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.Scheme.adicResidue_koszul_coefficient_augmentation`
(node `lem-sfb-adic-residue-koszul-coefficient-augmentation`).

Also proved `CategoryTheory.ringedNegativeKoszulLowDegrees`
(node `lem-sfb-negative-koszul-low-degrees`) and all private helpers.
There are zero `sorry` statements left in either delivered Lean module,
zero holes added, and zero obligations split off. The proof uses the existing
finite-coordinate and duality declarations as stage-3 dependencies; it does not
claim to remove their pre-existing proof obligations.

## No longer needed

No existing public import, node, or module is withdrawn. The item's old direct
proof dependency on `lem-cbc-signed-koszul-finite-coordinates` is now mediated by
the proved low-degree lemma; that coordinate theorem remains needed transitively.
The successor compatibility supplied by negative Koszul duality is not needed:
naturality follows from the normalized degree-zero units and quotient projections.
No Noetherianity, K-flatness, or derived pro-zero result is used.

The new low-degree module imports `SignedKoszulCompletionModel` publicly and
`SignedKoszulFiniteCoordinates` privately; it needs no negative-transition import.

## Where the brief, the DAG or earlier work was wrong

No statement was found false or changed. The planned finite-free argument required
an explicit low-degree interface for the actual ordered tensor, including the
single-complex equality transports and normalization of the empty basis. That
interface is now proved from the existing coordinate theorem, rather than left
as another augmentation obligation. The unit route is preserved. The calculation
covers the empty list, zero and unit sections, zero rings, and empty sites.

## New nodes

`lem-sfb-negative-koszul-low-degrees` records the proved two-term coordinate
calculation in `Sheaf.CategoryTheory.RingedNegativeKoszulLowDegrees`. It inherits
the item's chapter, unit, and blueprint ancestry. Its source is the finite free
negative Koszul complex of Stacks 0A0E and the sequence-Koszul construction. Its
Mathlib searches found generic complex and differential results but no matching
ringed Koszul coordinate theorem. No shared-definition change record is needed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
