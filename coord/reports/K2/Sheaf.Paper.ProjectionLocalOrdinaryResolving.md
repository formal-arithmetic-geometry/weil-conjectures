## What changed

Proved `AlgebraicGeometry.Scheme.ProjectionRestriction.localOrdinaryResolving_exists`
in `Sheaf.Paper.ProjectionLocalOrdinaryResolving`, with its statement unchanged.
All new helpers are private and fully proved in the item module. The public import
and all public definitions remain unchanged; added imports are proof imports.

The main construction first localizes the underlying-set inverse-image presentation.
It compares the two composite right adjoints through the product comparison and
proves the corresponding left-adjoint comparison carries the slice unit to the
restricted global unit. Existing module presentations then give the actual exact
pullback, its normalized ordinary tensor comparison, and resolving preservation.
Identity scalar extension is removed by its canonical unit isomorphism.
The item's DAG proof, proof dependencies and proof origin now describe this route.

Validation: the complete module compiled without warnings in 27.3 seconds.
`#print axioms localOrdinaryResolving_exists` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The check command was removed afterwards.
No finite-rank, nonzero-ring, point, nonempty-site, or boundedness assumptions
are introduced: the construction applies to every slice object and unbounded complex.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.ProjectionRestriction.localOrdinaryResolving_exists`
(node `lem-weil-pbc-projection-local-ordinary-resolving`).

Added 0 holes. Remaining holes in the delivery: none. Split-off statements: none.
This is a proof, not a decomposition. Its axiom closure has no `sorryAx`.

## No longer needed

No original imports were removed and no files are withdrawn. The following four
planned dependencies are unnecessary for this proof and are removed from its DAG
proof dependencies:

- `lem-weil-pbc-localize-ringed-site-morphism`
  (`Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`): the direct composite-adjoint
  localization works with the actual pro-etale object and morphism universes.
- `lem-pur-site-restriction-module-adjunction-exact`
  (`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`): exactness follows from
  the actual pullback's underlying abelian inverse-image presentation.
- `lem-weil-pbc-ringed-topoi-module-adjunction`
  (`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`): use Mathlib's
  actual module adjunction with the containing-universe existence theorem.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): this item needs
  only the ordinary binary tensor comparison, supplied by the proved
  `inverse_tensor_source_unit` helper of `SignedLinePullbackTensor`.

These modules may still serve other parents; no declaration is deleted.
The K-flat ringed-topos pullback dependency is retained. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned localization interfaces require equal site object and morphism universes,
so they do not directly instantiate on the raw pro-etale sites used in the statement.
The already proved containing-universe APIs and a set-sheaf version of the existing
composite-adjoint localization argument close the obligation without another split.
The large derived tensor comparison is stronger than the ordinary conclusion needed.

The current `prop-pur-kinjective-resolutions-exist` Lean record lists its newer mixed
universe companion and omits the preserved, already proved
`grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses` declaration.
This proof uses the latter with coefficient universe `u + 1`; no change to that
other node or module is needed for compilation.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
