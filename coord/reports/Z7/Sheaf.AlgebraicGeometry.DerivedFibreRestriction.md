## What changed

Proved `AlgebraicGeometry.Etale.derivedFiberMap_restriction` in
`Sheaf.AlgebraicGeometry.DerivedFibreRestriction`, following the existing node's two-step route.
Added proof-only imports of
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal` and
`WeilConjectures.AlgebraicGeometry.DerivedGlobalGermExchange`.

The proof applies horizontal exchange pasting, moves the inverse target germ past the
inverse-image composition comparison by naturality, and cancels the two inverse composition
maps. Stalk comparison coherence is proved on ordinary sheaves using representative germs,
the composition formula for adjunction units, and equality of points on iterated pullbacks.
A proved private localization lemma transports this coherence to bounded-below complexes.
The derived global-germ/exchange identity then identifies the remaining geometric-point
exchange with restriction; the identity-point germ cancels its inverse.

All auxiliary lemmas are proved and private. Existing public definitions, theorem statements,
and public imports retain their meanings and signatures. There are no consumer adaptations,
new modules, new nodes, or definition changes. The existing DAG route and proof dependencies
are unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.derivedFiberMap_restriction`
(node `lem-weil-pbc-derived-fibre-restriction`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0.
This is a proof, with no split-off obligations.

## No longer needed

None. Both declared proof dependencies are used: horizontal exchange coherence and derived
global-germ/exchange compatibility. No original import, node, or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect dependency was found. The phrase that natural stalk
comparisons identify the sources hides a substantial coherence calculation. This delivery
supplies that calculation, including the equality transports at the identity geometric point
and the exact-functor localization comparisons, without adding hypotheses.

The representative-germ unit calculation follows the existing proved argument in
`WeilConjectures.AlgebraicGeometry.UnderivedGlobalGermExchange`; the pullback-point calculation
follows the existing descent-transition germ argument in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentStalk`. The larger descent
module is not imported, since only its elementary proof pattern is needed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
