## What changed

Added `Sheaf.AlgebraicGeometry.EtaleGraphOpenTowerFactor`, a split-off
intermediate theorem expressing the graph tower identity after postcomposition
with the inverse endpoint comparison. The item theorem now imports this module
privately and proves the requested equality by cancelling that inverse
comparison and simplifying the isomorphism triangle. The original theorem
signature and public imports are unchanged.

Both modules compile in import order with `lcompile.py`.

## Proved and sorry left

The original hole
`AlgebraicGeometry.Etale.etaleGraph_open_tower` is closed by a real categorical
cancellation argument. One strictly simpler hole remains in
`AlgebraicGeometry.Etale.etaleGraph_open_tower_factor`, whose node is
`lem-pur-etale-graph-open-tower-factor`; it is the pre-endpoint-normalization
identity and omits the terminal comparison `k`.

No definitions contain `sorry`.

## No longer needed

No existing public import or existing node is withdrawn. The original proof
route is reduced to the factorization node plus cancellation; no additional
geometric dependency is introduced.

## Where the brief, the DAG or earlier work was wrong

The direct tower equality has no existing library theorem. The useful
intermediate is the identity before the terminal compactification comparison;
postcomposition with its inverse makes the endpoint normalization a separate,
strictly simpler statement. No target statement or definition was changed.

## New nodes

`lem-pur-etale-graph-open-tower-factor` records the pre-endpoint-normalization
factorization used by the item theorem and is attached to
`Sheaf.AlgebraicGeometry.EtaleGraphOpenTowerFactor`.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
