## What changed

Proved `AlgebraicGeometry.WeilSheaf.exists_geometrically_connected_clopen_support`
without changing its signature or its three public imports. Its proof takes the
connected component of x, proves that it also contains y, constructs its finite
constant field, and supplies the constant relative dimension, clopen immersion,
characteristic instance and lifts of the marked finite points.

Added two proved public lemmas in new modules:
`Sheaf.DeligneLaumon.IrreducibleLisseClopenSupport` and
`Sheaf.DeligneLaumon.SmoothAffineConnectedConstants`. The first is the clopen-support
argument alone, requiring neither smoothness nor affineness. It uses the kernel of
the native Weil restriction/direct-image unit, finite-etale preservation of
lissity, lisse kernels, the disjoint-support theorem and the adjunction triangle.
The second is the purely geometric constant-field argument, independent of Weil
sheaves and marked points. It constructs the integral closure of k in global
sections and proves its finiteness by evaluation in a finite residue field.
Normality identifies it with the algebraic constants of the function field.

The original module includes a proved private helper for constant relative
dimension: intersect the local smooth charts on the irreducible scheme, compare
their dimensions over a field, and glue the local structures. Both new modules
have nodes; the original node records the route actually used. No existing file
besides the item and its node was changed, and no consumer adaptation is needed.

Validation: `lcompile.py --all` compiled all three modules in import order with
exit code 0 and no warnings. The service's 60-second acceptance limit for Lean
execution was unchanged; its displayed elapsed times also include artifact setup
and cache waits outside that limit.

## Proved and sorry left

Closed the original 1 hole:
`AlgebraicGeometry.WeilSheaf.exists_geometrically_connected_clopen_support`
(node `lem-zl-geometrically-connected-clopen-support`).

Added 0 holes. Neither the original module nor either new module contains a
`sorry`. Both new public lemmas and both private helpers are proved. This is a
proof from existing declared dependencies, not a decomposition into new holes.
The constant-field proof uses the already stated
`AlgebraicGeometry.geometricallyIrreducible_of_isAlgebraic_mem`
(`lem-zl-field-extension-algebraically-closed-geometric`) and
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_geometricallyConnected`
(`lem-trf-geometrically-connected-image-criterion`); those existing declarations
still have their own holes and were not modified by this delivery.

## No longer needed

The item's proof does not use
`lem-zl-affine-geometric-components-finite-extension`, module
`Sheaf.DeligneLaumon.AffineGeometricComponentsFiniteExtension`.
It constructs the constants directly, without decomposing a base change or
descending a geometric component. Removed that dependency from this item's node;
no declaration or module is withdrawn, since other users may still need it.
There were no old private proof imports to remove. Kept the original public
imports verbatim. Removed the new redundant private imports
`WeilConjectures.PointCount` from the item (already public through Stalk) and
`WeilConjectures.WeilSheaf.StalkIso` from the support lemma (already public through
DirectImageRestriction and DirectImageStalk). Removed the redundant new private import
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic` after importing
`Mathlib.RingTheory.Algebraic.Integral`, which already provides it.
The support proof also uses the sheaf-level disjoint-support API directly,
so it does not import `WeilConjectures.WeilSheaf.Localization`.

## Where the brief, the DAG or earlier work was wrong

The old first proof step marked the clopen-support and regularity argument
as elementary with no dependencies. Arithmetic irreducibility here is simplicity
among lisse Weil subobjects, not simplicity among all constructible sheaves.
The proof therefore verifies lissity of the kernel explicitly. The normality and
constant-field step also needs real algebraic geometry; a decomposition after
base change alone does not produce a clopen immersion into the original scheme.
The delivery supplies that argument by an actual integral-closure construction.
The target statement and unit route are preserved, including dimension zero.

## New nodes

`lem-zl-irreducible-lisse-clopen-support` attaches the proved clopen-partition
lemma to `Sheaf.DeligneLaumon.IrreducibleLisseClopenSupport`. Its empty/full-open
edge cases are immediate; it assumes arithmetic, not geometric, irreducibility.

`lem-zl-smooth-affine-connected-constants` attaches the proved constant-field
lemma to `Sheaf.DeligneLaumon.SmoothAffineConnectedConstants`. ConnectedSpace
includes nonemptiness. The theorem changes the structure morphism of the same
scheme; it neither asserts a rational point over the constant field nor assumes
positive dimension. No change record is required: all existing interfaces stay
unchanged.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
