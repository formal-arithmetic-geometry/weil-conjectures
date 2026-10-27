## What changed

Proved `AlgebraicGeometry.Etale.rawRestrictedResolution_naturality` without changing
its statement. Private helpers identify chart precomposition with section restriction,
apply naturality of single-complex homology, undo the shift, and evaluate a chain representative.
The proof imports `RawRestrictedResolutionCocycle`, and uses the private represented
adjunction equivalence from `RawRestrictedHomotopySectionsIso` via `import all`.
Fullness of localization into the shifted K-injective resolution gives a chain
representative of each raw morphism. The existing shift square, cancellation of
the inverse augmentation, and the resolution-evaluation theorem identify its
normalized value with the evaluated chain cocycle. Precomposition gives the
representative at the other chart. Naturality of the represented generator,
single-complex homology, and the cocycle isomorphism then gives the required square.
No adopted source module is changed. The complete proof and the delivery axiom probe passed in 56.6 seconds.
Explicit comparison objects and types avoid repeated expensive conversions during
kernel checking. The delivered file has no profiling settings or diagnostic commands.

## Proved and sorry left

Closed the sole hole in `AlgebraicGeometry.Etale.rawRestrictedResolution_naturality`.
No holes added; no holes remain in this module. A direct `#print axioms` of the
new proof reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The proof uses the existing
`AlgebraicGeometry.Etale.rawRestricted_resolution_shift_square` (node
`lem-weil-pbc-raw-restricted-resolution-cocycle`), now proved in the shared source.

## No longer needed

No original imports removed and no module withdrawn. The direct generator calculation
does not need node `lem-weil-pbc-single-homotopy-presheaf-homology` or module
`WeilConjectures.CategoryTheory.SingleHomotopyPresheafHomology`: functoriality of
the single-complex homology comparison replaces the Hom-complex argument.
The proof also does not call
`injective_upperStar_obj_of_etale_addCommGrp` separately: preservation of injectives
and K-injectivity of the shifted restriction are encapsulated by the existing
`RawRestrictedResolutionCocycle` infrastructure. Thus
`lem-sbc-etale-abelian-restriction-injectives` is no longer a direct proof dependency
of this node; it remains needed below that infrastructure. The other original proof dependencies
are used, including their explicit construction lemmas.

## Where the brief, the DAG or earlier work was wrong

The original plan described undoing shifts without listing the already stated
`lem-weil-pbc-raw-restricted-resolution-cocycle`. The proof now records that dependency
explicitly. The fixed proper-base-change unit route is preserved. No statement or
definition repair, no new nodes, and no change to any target statement.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
