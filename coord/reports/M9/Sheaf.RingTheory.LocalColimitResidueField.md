## What changed

Proved `CommRingCat.local_colimit_residue_field` in
`Sheaf.RingTheory.LocalColimitResidueField`, preserving its signature. The proof uses
Mathlib's concrete filtered-colimit representatives and eventual equality to show
that the cocone maps reflect units. The one-minus-unit characterization proves
locality; maximal-ideal contraction and representation give the union formula.
The residue-field maps are injective ring maps between fields. Compatible maps to
an arbitrary commutative ring descend from the original colimit and then factor
through its residue field; representatives prove uniqueness.

Updated the node's proof and proof origin to describe this route. All three
existing proof dependencies are retained. No new public declarations, interface
changes, or adaptations of consumers are needed.

## Proved and sorry left

Closed the one original hole in `CommRingCat.local_colimit_residue_field`
(`lem-sfb-local-colimit-residue-field`). Added zero holes; split off zero statements.
No `sorry` remains in the delivery.

## No longer needed

Removed the redundant proof import
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`: it is already available through
the public residue-field import. No DAG nodes or project modules are pruned. The direct construction and closure
checks for a separate union ideal in the original proof plan are unnecessary:
unit reflection gives the local maps first, and the existing maximal-ideal API
then gives the union formula. All stated mathematical dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The omitted argument in Stacks Tag 04GI can be
formalized without introducing a separate ideal: Mathlib defines maximal ideals
of local rings as nonunits and provides the local-hom contraction API.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
