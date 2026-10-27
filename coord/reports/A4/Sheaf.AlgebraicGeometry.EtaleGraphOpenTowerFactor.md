## What changed

Proved `AlgebraicGeometry.Etale.etaleGraph_open_tower_factor` without changing its
statement or public imports. The proof combines compactification factorization,
proper postcomposition, compact-support associativity and inverse-conjugate
composition. The inverse-image square comparison cancels the intermediate
factorization, giving exactly the two adjunction maps in the original statement.

Added `Sheaf.AlgebraicGeometry.EtaleGraphEtaleOpenComposition`, containing the proved
`AlgebraicGeometry.Etale.graph_etale_open_composition`. This is the etale/open portion
of the tower, with no proper postcomposition or auxiliary square. It follows from
the existing support/sum compositor, graph refinement for the identity-proper
compactification, and the sum-composition counit theorem. Private helpers identify
the two constructions of the derived open adjunction and transport the chosen
compactification compositor using its tower and cocycle equations.

Updated the item's node to this route and added the helper's node. No existing
module or node besides the assigned item's was changed.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.Etale.etaleGraph_open_tower_factor`
(`lem-pur-etale-graph-open-tower-factor`).

Added zero holes. `AlgebraicGeometry.Etale.graph_etale_open_composition`
(`lem-pur-graph-etale-open-composition`) and every private helper are proved.
Neither delivered Lean module contains `sorry`.

The proof reuses the existing `etaleSupportSumCompositor`, whose component theorem
is a pre-existing dependency with an unfinished proof. This delivery introduces no
replacement or restatement of that dependency.

## No longer needed

No modules withdrawn and no original imports removed. The original graph sheaf
normalization is no longer a direct proof dependency of this item, but remains
needed through graph coherence; it is not claimed as pruned. All unit statements
and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged. The planned sheaf-section calculation can be replaced
by the existing support/sum compositor and graph refinement equations. The etale
sum and open extension functors have the same underlying sheaf construction, but
their derived adjunctions use different constructions; their agreement requires
the counit calculation included here.

## New nodes

`lem-pur-graph-etale-open-composition` realizes the proved helper in
`Sheaf.AlgebraicGeometry.EtaleGraphEtaleOpenComposition`. It is strictly the
etale/open composition step before proper postcomposition. Identity and empty
opens and zero coefficients are covered by the same invertibility, adjunction,
and composition identities. There are no change records because no existing
signature or definition was changed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
