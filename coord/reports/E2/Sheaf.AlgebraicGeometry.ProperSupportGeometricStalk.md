## What changed

Added `Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore`, isolating the geometric
injectivity and exact-range assertion needed by the support-image construction. The original
module now imports this core and proves `properSupport_geometricStalk_image` by taking the
linear range and applying `LinearEquiv.ofInjective`; the canonical factorization is checked by
`ModuleCat.hom_ext`. The image node proof and dependencies were updated accordingly.

## Proved and sorry left

`AlgebraicGeometry.Etale.properSupport_geometricStalk_image` is proved. One geometric hole is
left in `AlgebraicGeometry.Etale.properSupport_geometricStalk_image_core` (node
`lem-cbc-proper-support-geometric-stalk-image-core`), whose statement gives injectivity of the
restriction map and identifies its linear range with properly supported fibre sections.

## No longer needed

The image proof no longer directly imports or depends on the locality, compactification, or
extension-by-zero nodes listed in the original image node; those geometric dependencies are
concentrated in the new core theorem. No existing module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original image node treated the full support-image and extension-by-zero argument as if it
could be assembled directly from declarations already available to the module. The available
Lean declarations do not expose the required injectivity and surjectivity-on-proper-support
statement, so that geometric part had to be recorded as a separate strictly smaller node.

## New nodes

`lem-cbc-proper-support-geometric-stalk-image-core` records the geometric core: injectivity of
the restriction map and the exact characterization of its linear range. Its proof follows Tag
0F76's representative, support-locality, shrinking, compactification, and zero-extension
argument; the remaining theorem combines it with elementary linear algebra.

The import/interface change is recorded in `coord/changes/ProperSupportGeometricStalk-import.md`.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
