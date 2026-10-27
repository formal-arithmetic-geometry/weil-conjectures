## What changed

Filled `AlgebraicGeometry.ProEtale.SemilinearProperOpen.scalarRestriction_ordinaryOpenSupported`
without changing its statement. Added proved private helpers only, in the assigned module.
The proof restricts both systems to strict integer-module towers, uses the existing
ordinary scalar-adjunction comparisons, and detects open support by the counit.
The initial integer sheaf makes arbitrary ambient ring-system maps compatible with this
restriction. Its component comparisons preserve all adjacent transitions.
The node records this shorter proof route. No shared interface or consumer changes.
Validation: the complete module compiled through lcompile.py in 23.9 seconds with no
errors or warnings; the assigned theorem signature is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.scalarRestriction_ordinaryOpenSupported`
(node `lem-pur-semilinear-open-restriction-support`). No holes added; none remain in the
assigned module. The proof uses the already-stated
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarAdjunctions`, whose existing hole
belongs to `lem-sf-semilinear-scalar-adjunctions`; this delivery does not change it.

## No longer needed

The direct proof dependencies of this node no longer include
`lem-pur-site-restriction-module-adjunction-exact`
(`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`): the proof uses the existing
normalized integer scalar-adjunction package instead of constructing a new localized
extension isomorphism. This does not withdraw that node or module: the scalar-adjunction
package and other consumers still need it. No existing imports or modules were removed.
The unit statement and its realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The planned localization construction was unnecessary
for this node once the existing normalized integer scalar-adjunction package was used.
The argument covers the empty open, the identity open, arbitrary transition maps and
arbitrary ambient coefficient-system maps; it assumes no flatness.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
