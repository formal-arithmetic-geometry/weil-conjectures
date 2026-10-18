## What changed

Proved `AlgebraicGeometry.finitePresentation_of_finite_over_locallyNoetherian` in
`Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian` by assembling the
three existing Mathlib instances. The signature, visibility, imports and docstrings are
unchanged. The DAG proof plan is unchanged: finiteness supplies locally finite type and
an affine morphism; the Noetherian-target instance supplies locally finite presentation;
affineness supplies quasi-compactness and separatedness, hence quasi-separatedness.

The proof compiles successfully through `lcompile.py` (2.0 seconds). Mathlib sources read:
`AlgebraicGeometry/Noetherian.lean` (the instance preceding
`LocallyOfFinitePresentation.iff_locallyOfFiniteType`),
`AlgebraicGeometry/Morphisms/Finite.lean`, `Morphisms/Affine.lean`, and
`Morphisms/Separated.lean`. LeanFinder found `IsFinite.instLocallyOfFiniteType` and
`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`; Loogle found the finite-presentation
class and its standard instances; the logged grep located the Noetherian equivalence.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.finitePresentation_of_finite_over_locallyNoetherian`
(node `pqf-lem-finite-fp-locnoeth`). Proved 1 of 1 sorries; added 0 holes; split off 0.
No sorries remain in the delivered module. No other modules are changed.

## No longer needed

None. Both existing imports are required: `Mathlib.AlgebraicGeometry.Noetherian` supplies
the Noetherian-target finite-presentation instance and
`Mathlib.AlgebraicGeometry.Morphisms.Finite` supplies finiteness and its consequences.
The proof uses the facts of all the stated DAG dependencies, directly through Mathlib's
instances; no planned node or module is pruned. No additional proof import is needed.

## Where the brief, the DAG or earlier work was wrong

The node's historical split report says that no sorry-free project declaration states the
item. The current source library already has the identical conjunction as
`AlgebraicGeometry.IsFinite.locallyOfFinitePresentation_of_isLocallyNoetherian` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite`, with precisely the same
instance-based proof. Importing that larger module is unnecessary: the item's existing
Mathlib imports suffice. The existing DAG proof plan accurately describes this proof.
The unit realization record imposes no additional dependency on this elementary assembly.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
