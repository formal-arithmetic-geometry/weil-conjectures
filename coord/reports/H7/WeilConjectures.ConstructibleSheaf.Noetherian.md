## What changed

Filled the two theorem holes in
`WeilConjectures.ConstructibleSheaf.Noetherian`, preserving all existing declaration
signatures, attributes, public imports, definitions, and existing proofs.
Added a proved private categorical helper transporting monicity across natural
isomorphisms; this prevents repeated unfolding of sheaf pullback constructions.
Added the proof-only import
`WeilConjectures.AlgebraicGeometry.IrreducibleStratificationRefinement`.

`AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`
uses the existing topological irreducible-refinement theorem and the existing
finite-local-constancy API for refinements. Immersion images transfer irreducibility
of the domains to irreducibility of the strata.

`AlgebraicGeometry.Etale.exists_finset_mono_pi_lift` follows the blueprint's finite
irreducible lisse partition argument. At the image of each generic point, choose one
map for every nonzero element of the finite source stalk. Their finite union gives
a product map injective at each generic stalk, by its projection identities. Lift
the algebraic-closure points through the stratum immersions; the existing generic
kernel theorem proves monicity on each stratum. Naturality of the pullback/stalk
comparison and stalkwise extensionality then prove monicity globally. This also
handles the empty scheme, zero stalks, and empty selected index set.

Searched with Lean Finder for Noetherian irreducible refinements, Loogle for finite
injective selection, and rg across the source library, Sheaf modules, and Mathlib.
Used the existing proved refinement theorem rather than introducing any new result.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`
  (blueprint `lem-weil-pbc-irreducible-lisse-strata`).
- `AlgebraicGeometry.Etale.exists_finset_mono_pi_lift`
  (blueprint `lem-weil-pbc-constructible-noetherian-finite-selection`).

No sorry remains in the item. No holes added and no statements split off.
The module compiled cleanly in 49.1 seconds. A separate `#print axioms` check
reports `sorryAx` transitively for both declarations, alongside the standard
axioms: these proofs close the local holes using existing library results; they
do not claim the entire dependency closure is already proved.

## No longer needed

None. No public imports or existing declarations were removed. The proofs keep the
irreducible refinement, generic-kernel, and conservative-stalk route. No dependency
module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The current DAG has no node whose `lean.module` is
this adopted source module: its docstring blueprint nodes attach to earlier
abelian/set-sheaf declarations in other modules. The source module's module-sheaf
proofs use the same finite-partition route, so those other declaration attachments
and their proofs were left intact. No source signature or target meaning changes.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
