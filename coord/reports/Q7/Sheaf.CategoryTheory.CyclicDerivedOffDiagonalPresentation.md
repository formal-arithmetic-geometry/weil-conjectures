## What changed

Filled `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedOffDiagonalPresentation_unique`
in the item module, preserving every existing declaration signature and definition.
All added helpers are private and proved. Added proof imports of
`Sheaf.CategoryTheory.FreeDerivedWeilResolution` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`.

The proof uses the existing cyclic free resolution. Evaluation on summand zero
shows that the free adjuncts of the splitting and off-diagonal map define a map
of short exact sequences. Applying the action to the negative-summand equation
proves its first commuting square with the specified sign. The canonical SES
boundary then equals a pairing built from the localized free boundary and counit.
Naturality of these transformations handles arbitrary derived endpoint maps.
The canonical shift unit unshifts each target endpoint map, and the shift triangle
identity recovers the native boundary. Both presentations therefore give the same
pairing of the prescribed underlying morphism.

The proof keeps the underlying and fixed-pair derived Hom universes independent.
Only the chain resolution data are obtained using auxiliary small derived models;
the free boundary is then descended into the originally chosen localization.
The existing DAG node's uniqueness proof step now records this completed argument,
including the existing `def-weil-exact-derived-adjunction` tool for the localized
counit with independent universes. Its concrete constructor is already proved;
using it preserves the unit route.
No other existing module or node was changed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedOffDiagonalPresentation_unique`
(node `lem-sf-cyclic-derived-off-diagonal-presentation`).

Holes closed: 1. Holes added: 0. Split-off statements: 0.
There are no remaining `sorry` declarations in the item module.
Compilation and delivery validation are recorded by the delivery tool.

## No longer needed

None. No imports or planned dependencies were removed. The proof follows the
existing free-resolution comparison route; no modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing free-resolution theorem uses
a common derived Hom universe, whereas this item allows two independent universes.
The proof reuses its chain-level data and descends the free boundary with the
existing localization API in the required universe. No shared interface change
was needed.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
