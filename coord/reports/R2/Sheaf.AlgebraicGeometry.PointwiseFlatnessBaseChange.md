## What changed

Proved `AlgebraicGeometry.pointwise_flatness_base_change` in
`Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange`, with its signature unchanged.
The proof constructs the actual commuting square of stalk ring maps, including
transport between the two equal base points, and the canonical tensor-product
map to the pullback stalk. It applies `pullback_stalk_tensor_flat`, tensor-product
base change and symmetry, composition of flat ring maps, faithful flatness of a
flat local homomorphism, and flat permanence. The existing imports all remain
needed. No definitions, public imports, source-library declarations or nodes change.

The server compiler accepted the complete proof without warnings. A direct
`#print axioms` on this proof reports exactly `propext`, `Classical.choice` and
`Quot.sound` (2.7-second verification compile).

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.pointwise_flatness_base_change`
(node `lem-sfb-pointwise-flatness-base-change`). Proved 1 of 1 original sorries.
Zero sorries remain in the item; zero holes added and zero statements split off.

## No longer needed

None. All declared proof dependencies are used, and all existing imports are
retained. The proof follows the node's four steps and preserves the unit route.
The tensor flip and transitivity steps use the proved Mathlib ring-homomorphism
interfaces to the same module-flatness results.

## Where the brief, the DAG or earlier work was wrong

None. The stated dependencies suffice. The equality of the two base points must
be transported explicitly through `stalkCongr`; the existing tensor-stalk lemma
already requests exactly this transport.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
