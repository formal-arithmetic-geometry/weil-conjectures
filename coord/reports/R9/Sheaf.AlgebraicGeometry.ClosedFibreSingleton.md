## What changed

Proved `AlgebraicGeometry.preimage_singleton_eq_empty_or_singleton_of_injOn_closedPoints`
in `Sheaf.AlgebraicGeometry.ClosedFibreSingleton` directly from Mathlib's Jacobson-space
API. The closed fibre contains a closed point if nonempty; injectivity identifies its
closed points with a singleton, and density identifies the whole fibre with that singleton.
The theorem signature and all public imports are unchanged. Updated its proof docstring
and DAG proof, proof_deps, and proof_origin to record this shorter argument.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.preimage_singleton_eq_empty_or_singleton_of_injOn_closedPoints`
(node `lem-sc-point-tangent-closed-fibre-singleton`). Added 0 holes; 0 remain in the item.
There are no split-off lemmas. The proof uses only Mathlib declarations.
The final single-file lcompile.py check passed without warnings (3.0 seconds).

## No longer needed

Removed the private import `Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterClosureSingleton`.
Removed the proof dependency `lem-sc-finite-type-nonclosed-closure-closed-points`
(`AlgebraicGeometry.infinite_closedPoints_inter_closure_singleton`). Its infinite-specialization
argument and its positive-dimension dependency
`lem-sc-positive-dimensional-locally-algebraic-closed-points`
(module `Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterOfTopologicalKrullDimPos`)
are unnecessary for this proof: density of ambient closed points suffices.
Consequently this proof also needs none of that module's proof imports:
`Sheaf.AlgebraicGeometry.ClosedPointOfAffineOpen`,
`WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic`,
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`, or
`Sheaf.RingTheory.InfiniteSetOfIsMaximalOfRingKrullDimPos`.
These are dependency removals from this item, not withdrawals: other consumers may need them.
The replacement dependency is the existing Mathlib leaf
`lem-sc-lft-over-field-jacobson-space`. No declaration or module is deleted.

## Where the brief, the DAG or earlier work was wrong

The planned argument is valid but unnecessarily uses infinitude of closed specializations.
The same closed-fibre assertion from Stacks Tag 0E8S follows directly from the Jacobson
property in Tag 0478(2). This is a change below the unit level: the closed-fibre step of
point separation, and the Riemann–Roch unit's route, remain intact.
No statement or definition repair was needed. Empty fibres and empty sources take the
first alternative; in the nonempty case the chosen point is closed in the ambient source,
not merely in the fibre. All original hypotheses remain.

Searches through msearch.py: LeanFinder found LocallyOfFiniteType.jacobsonSpace;
Loogle did not recognize closure_inter_closedPoints; grep found that class field and
its locally finite type application. Their signatures were checked in the pinned Mathlib.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
