## What changed

Replaced the proof hole in `AlgebraicGeometry.ProEtale.diagonalTower_directImage`.
The proof constructs the four total right derived functors with their shifts and
triangulated structures, defines normalized derived-limit projections by the
universal property, derives the levelwise evaluation comparisons, and applies the
existing composite-derived-functor comparison. A separate equality proof shows that
this comparison respects every canonical tower projection.

The fixed-scalar inverse-image functor is exact. Its adjunction, applied levelwise
to strict towers, proves the K-injective preservation needed for the composite
comparison. Thus the argument takes place directly in the published `DiagonalMod`
categories. All new helpers are private and proved. The only new imports are private
proof imports of `RingedStrictTowerHomotopyLimit` and
`RingedTowerPushforwardLimitComparison`, using their generic proved helpers.

Updated the direct-image proof step of `det-prop-diagonal-tower-limit` and its
proof-dependency union to match this construction. Existing public signatures,
definitions and public imports are unchanged. Local irreducibility attributes
prevent unnecessary expansion of comparison maps, normalization specifications,
and standard derived-category constructions. A local instance priority selects
Mathlib's proved `hasExt_of_enoughInjectives` for Ext-smallness; the attribute is
not exported. Elementary private diagram lemmas keep the projection argument
independent of the syntactic presentation of evaluated complexes.

A temporary `#print axioms` check confirmed that `diagonalTower_directImage` depends
only on `propext`, `Classical.choice`, and `Quot.sound`; the diagnostic command was
removed. Delivery runs compilation with the project's axiom probe and packet checks.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.ProEtale.diagonalTower_directImage`
(node `det-prop-diagonal-tower-limit`).

The one remaining hole is unchanged:
`AlgebraicGeometry.ProEtale.diagonalTower_limit`
(node `det-prop-diagonal-tower-limit`). Its existing docstring retains the source
and the complete intended argument. No holes were added or split off.

## No longer needed

No existing Lean imports or modules were removed. No module is claimed pruned.
The direct-image proof no longer needs an explicit conversion to a morphism of
ringed topoi: its generic K-injective argument applies directly to fixed-scalar
module sheaves. Accordingly `def-weil-pbc-ringed-topos-morphism` was removed from
that proof step and from the proof-dependency union. The ringed-topos module remains
in the transitive import closure of the generic comparison library.
All dependencies of the untouched completed-limit argument remain recorded.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-site theorem uses `SheafOfModules` categories, whereas this item
uses sheaves valued in `ModuleCat`. Its generic comparison helpers apply directly
to the latter presentation, so the proof does not require a new equivalence between
the presentations. There is no statement correction or definition repair.

The proof explicitly invokes the existing nodes
`lem-weil-tower-evaluation-kinjective` and
`lem-weil-pbc-right-adjoint-preserves-kinjective`, already dependencies of the
planned generic comparison node. These are exact categorical tools for evaluation
and the whiskered exact inverse-image adjunction; they do not replace the unit's
route.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
