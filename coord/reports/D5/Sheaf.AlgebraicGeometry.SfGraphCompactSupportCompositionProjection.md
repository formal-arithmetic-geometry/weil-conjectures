## What changed

Proved `AlgebraicGeometry.Etale.sfGraphCompactSupportCompIso_projection` from the existing
`sfEtaleCompactProjectionForward_composition`, specialized to the three chosen
compactifications. The proof converts only the tensor-map and compactification APIs. Private metaprogramming
helpers normalize these APIs and build ordinary congruence/proof-irrelevance terms,
which are checked by Lean's kernel. This follows the technique already used in
`SfEtaleCompactProjectionCoherence` and upstream `LowerShriekCompositionCoherence`.
Replaced the private proof import of `SfEtaleCompactProjectionCoherence` by
`SfEtaleCompactProjectionForward`; updated the node's proof route accordingly.
The theorem signature and all public imports are unchanged. Local instance priorities
align the coefficient and sheaf braidings with the existing tensor APIs; local
irreducibility keeps the large derived constructions folded.

Searches: LeanFinder returned ordinary pushforward-composition declarations, Loogle
returned generic whiskering declarations, and the Mathlib grep found no specialized
match. Local `rg` located the existing forward-square theorem. The new proof import
passes `tools/import_direction.py may`.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.Etale.sfGraphCompactSupportCompIso_projection`
(node `lem-r9-graph-compositor-projection`). No holes added or split off.
No `sorry` remains in the delivered module. The final individual-file compile via
`lcompile.py` succeeded without warnings in 10.9 seconds (under the 60-second limit). This proves the item from an existing
library theorem; its downstream dependencies retain their own proof obligations.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.SfEtaleCompactProjectionCoherence`.
The proof no longer directly uses node `lem-sf-etale-compact-projection-coherence`
or node `lem-sf-etale-ambient-adjoint-projection`: the already established forward
square avoids the inverse-projection cancellation argument. The latter remains a
transitive dependency of the forward-square library, so no global withdrawal is claimed.
No module is withdrawn, and the public statement imports stay unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned inversion of the inverse-composition equation was unnecessary:
`sfEtaleCompactProjectionForward_composition` already supplies its forward version
for exactly the specified graph compositor and arbitrary supplied compactifications.
The delivery preserves the statement and the unit route.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
