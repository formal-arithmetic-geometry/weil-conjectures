## What changed

Replaced the proof of
`WeilConjectures.PurCompactSupport.openProjectionFactor_compositor_transport`.
Its statement and public imports are unchanged. The first equation follows by
naturality of `openComparison` and `scalarTensor`, using compatibility of
`scalarPull` with the geometric compositor. The second follows by naturality of
`openProjectionIso`, commuting the independent maps in the product category.

Added `Sheaf.Paper.ScalarGeometricPullComposition`, proving the scalar-only
composition equation. Its proof establishes the ordinary restriction/pullback
square by taking geometric mates and checking the right-adjoint square on
sections. It then localizes the exact square, identifies the prescribed
`scalarPull` with its scalar mate, and pastes mates. The new private categorical
helpers are fully proved. The open-projection naturality calculation is proved
locally; the exact-localization and ring-sheaf mate lemmas use proof-only imports.
No shared definition is changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurCompactSupport.openProjectionFactor_compositor_transport`.
Also proved the new theorem
`WeilConjectures.PurCompactSupport.scalarPull_geometric_composition`
(node `lem-sf-scalar-geometric-pull-composition`).
There are zero remaining holes in the delivery and zero holes added.
The imported existing statements are used as provided by the stage-3 library.

## No longer needed

No original import, existing node, or existing module is pruned. The original
coefficient-data dependency remains necessary. The new proof needs no auxiliary
open projection coefficient-change statement and introduces no replacement hole
for the transport obligation.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan did not supply the compatibility equation
between the specifically normalized scalar comparison and geometric compositor.
That equation is now proved in its own module, with the normalization and mate
pasting made explicit. The item is preserved with its original Lean attachment;
its rework row was read before copying. The current source has one hole and no
direct false-tail import. No quarantined module is withdrawn.

## New nodes

`lem-sf-scalar-geometric-pull-composition` records the proved scalar/pullback
composition equation, independent of tensor models and compactifications. It
uses the existing coefficient data, ring-sheaf coefficient-change adjunction,
and exact-square composition theorem. The original item's proof dependencies
and proof text now describe the naturality calculation actually used.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
