## What changed

Proved `AlgebraicGeometry.ProEtale.finiteCompactSite_tower_independence` in
`Sheaf.Paper.FiniteCompactSiteCoherence`, with its statement unchanged. Precompose
both tower maps with the same invertible source comparison and apply
`finiteCompactSiteCoherence` for the two towers. Solving that comparison equation
expresses the computed map as a composite of isomorphisms, proving invertibility.
All changes are confined to this theorem's proof. The module compiles in 11.8 s.

## Proved and sorry left

Closed one of the five original holes:
`AlgebraicGeometry.ProEtale.finiteCompactSite_tower_independence`.
This is a proof from the already stated composition comparison equation, which
still has its original hole; no claim of eliminating its transitive sorry is made.
Added zero holes and split off zero statements.

Four original named theorem holes remain, all attached to
`lem-sp-finite-compact-site-coherence`:

- `AlgebraicGeometry.ProEtale.finiteCompactSiteCoherence`.
- `AlgebraicGeometry.ProEtale.finiteCompactSite_naturality`.
- `AlgebraicGeometry.ProEtale.finiteCompactSite_composition_units`.
- `AlgebraicGeometry.ProEtale.finiteCompactSite_associativity`.

## No longer needed

None. No imports, declarations, modules or DAG dependencies are removed. The
remaining composition and coherence clauses retain the existing route through
finite-site tower pasting and the normalized etale composition laws.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing node's tower-independence argument works
as stated: cancellation of the two source comparison factors proves independence,
and solving for the computed map proves invertibility. Work on the other clauses
was not retained: matching explicit tower coordinates to the supplied
compactifications produced associator mismatches and expensive elaboration.
The delivered module contains only the checked tower-independence proof, and
preserves all original statements, definitions and imports.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
