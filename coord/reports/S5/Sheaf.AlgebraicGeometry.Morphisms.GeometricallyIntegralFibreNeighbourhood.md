## What changed

Proved `AlgebraicGeometry.exists_geometricallyIntegral_fibre_neighbourhood` without changing
its statement. First convert the given geometric irreducibility into geometric connectedness.
Apply `exists_smooth_geometricallyConnected_fibre_neighbourhood`, retaining its exact witnesses,
compactness and embedded fibre equality. Use `smooth_connected_fibre_normal_integrality`
for every point and residue-field extension, then Mathlib's geometric and fibrewise criteria
to obtain the required geometric integrality. The proof follows the three steps of the
current item node. Updated the previously stale declaration proof description to match them.
All public imports and the existing signature are preserved; only proof imports changed.
The final module compiled through `lcompile.py` without errors or warnings in 2.8 seconds.
The field-extension criterion is given its base ring explicitly; integrality is transported
from the chosen pullback to any cartesian representative by `IsIntegral.of_isIso`.

Read the dependency declarations, Stacks `more-morphisms.tex`,
`lemma-normal-morphism-irreducible` (057J), and the current blueprint unit
`sec-trace-formula/sk-i-curve-zero`. Ran LeanFinder, Loogle and Mathlib grep through msearch,
and searched both source-library trees. The source library also has the smooth connected
geometric irreducibility/reducedness route, but the current stated fibre-normal-integrality
lemma already supplies the required field-extension conclusion without introducing nodes
or importing the larger Riemann--Roch module.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.exists_geometricallyIntegral_fibre_neighbourhood`
(node `lem-trf-geometrically-integral-fibre-neighbourhood`).
There are zero holes left in the delivered module, zero added holes, and zero split-off
statements. This is a proof from the already stated dependencies, which remain separate items:
`AlgebraicGeometry.exists_smooth_geometricallyConnected_fibre_neighbourhood` and
`AlgebraicGeometry.smooth_connected_fibre_normal_integrality`. Their source files are unchanged.

## No longer needed

Removed the following direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore`.
- `Sheaf.AlgebraicGeometry.Morphisms.GeometricallyConnectedFibreNeighbourhood`.

The existing smooth-spreading and fibre-integrality modules encapsulate these inputs, so no
withdrawal of those modules is requested. Every proof dependency of the current item node
is still used; no DAG nodes or modules are pruned from its stated route.

## Where the brief, the DAG or earlier work was wrong

The current DAG is consistent with the proof. The module's old imports and five-step docstring
predated its split into smooth connected spreading and fibre normal integrality. The proof
imports and docstring now follow the current three-step node. No statement or definition
repair, consumer adaptation, or new node was needed.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
