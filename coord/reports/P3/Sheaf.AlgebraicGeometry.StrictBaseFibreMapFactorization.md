## What changed

Constructed the canonical strict-local comparison in the new module
Sheaf.AlgebraicGeometry.StrictLocalDerivedRestriction. The underlying restriction is
chosen only from the unique section-cone universal property, its naturality is proved,
and its derived comparison is an explicit composite of germ restriction, exchange,
Leray and the canonical single-functor coefficient comparison. No data is postponed.

Proved underived and derived specialization normalization at the distinguished closed
lift in Sheaf.AlgebraicGeometry.ClosedLiftStalkSpecialization, by initial pointed-germ
colimit extensionality, point evaluation, and right-derived identity functoriality.

Reduced strictBaseSheafFiberMap_factorization to two separate compatibility identities:
derived specialization through strict-local sections, and the arbitrary cartesian-square
fibre restriction identity. The combining proof constructs the witness explicitly,
uses naturality of the derived unit and Leray to transport the coefficient comparison,
and specializes to the closed lift for the second conjunct. All existing signatures,
public imports, definitions, and source-library modules are preserved.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Etale.strictBaseSheafFiberMap_factorization (node
lem-weil-pbc-strict-base-fibre-map-factorization) by decomposition.
Added two holes, each the whole proof of a named public theorem in its own module:

- AlgebraicGeometry.Etale.derivedEtaleStalkSpecialization_restriction
  (lem-weil-pbc-derived-specialization-restriction).
- AlgebraicGeometry.Etale.derivedFiberMap_restriction
  (lem-weil-pbc-derived-fibre-restriction).

This is a decomposition, not a net hole reduction: one hole closed, two added.
The item itself has zero holes. Both
AlgebraicGeometry.Etale.etaleStalkSpecialization_closed and
AlgebraicGeometry.Etale.derivedEtaleStalkSpecialization_closed are proved without new
holes. All three definitions in StrictLocalDerivedRestriction have complete bodies.

## No longer needed

Removed the item's private imports of
WeilConjectures.AlgebraicGeometry.DerivedGlobalGermExchange,
WeilConjectures.SixFunctors.BaseChange.DerivedPasting,
Sheaf.Paper.StrictHenselizationPointEvaluationPointed,
WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm,
Sheaf.AlgebraicGeometry.StrictHenselizationRestriction, and
Sheaf.AlgebraicGeometry.PointedEtaleStalk. Point evaluation and inverse-image germs are private imports of the proved closed-lift
module. DerivedGlobalGermExchange and horizontal pasting are recorded dependencies of
the separate exchange lemma's proof plan; their unused imports were removed from its
statement module as well. The retired empty SHEAF restriction
module and the coefficient-general PointedEtaleStalk interface are not needed anywhere
in this proof; this proof uses the generic pointed-section cone and Mathlib's abelian
sheafFiber. No existing module is withdrawn or globally claimed pruned.

The old proof_deps entry lem-weil-pbc-derived-exchange has no node in the current tree.
The new exchange lemma uses the existing actual nodes
lemma-weil-pbc-derived-exchange-coherence and lem-weil-pbc-derived-global-germ-exchange.
The canonical adopted strictLocalization restriction module is not needed: the statement
uses the different small strictHenselizationScheme model, handled by strictLocalSectionCone.
All unit-level statements and route steps are retained.

## Where the brief, the DAG or earlier work was wrong

The item node's old proof was one unformalized combined paragraph, and cited the missing
lem-weil-pbc-derived-exchange identifier. The current generic section-cone API supplies
restriction on the small model; the old private SHEAF restriction import is an empty
withdrawn module. The adopted canonical restriction concerns strictLocalization instead
of the small model and cannot be substituted definitionally. The new construction uses
the correct model throughout. No mathematical statement has been changed.

## New nodes

- def-weil-pbc-small-model-derived-restriction records the explicit canonical comparison,
  its natural germ restriction, and its derived restriction; no holes.
- lem-weil-pbc-closed-lift-stalk-specialization records both proved normalization identities.
- lem-weil-pbc-derived-specialization-restriction is the strictly smaller identity for
  specialization alone, on any bounded-below complex and without f or fibre maps.
- lem-weil-pbc-derived-fibre-restriction is the separate arbitrary-square exchange and
  restriction identity, without strict henselization or specialization.

Validation: all five modules compile individually through lcompile.py --all, including
the assembled item (44.3 seconds). The closed-lift module has no holes, the construction
module has no holes, and exactly the two named compatibility theorems remain open.

Each node has its source, full proof in words, Lean attachment and the three search kinds.
Searches found only topological/structure-sheaf specialization in Mathlib and the generic
project exchange/pasting tools, not these combined identities. No change record is needed:
only the item's proof and private imports, its proof record, and new modules are changed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
