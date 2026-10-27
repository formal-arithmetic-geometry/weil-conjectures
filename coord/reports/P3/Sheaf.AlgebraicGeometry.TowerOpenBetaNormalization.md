## What changed

Proved `openBetaRestriction_normalized` from the new, strictly smaller
`towerSquare_unit_sections` theorem. The Lean combination computes the exchange
mate on unit sections, moves the counit by naturality, cancels it by the triangle
identity, and compares the site arrows by their fibre-product projections.
Invertibility uses the existing `openBetaModule_normalized` theorem independently
of the section computation. No existing public signature or definition changed. The existing open-unit
isomorphism proof now shares a proved private helper at its two occurrences,
avoiding repeated elaboration of the same adjunction comparison.

The new module explicitly constructs its unit-section and site-square data.
Its remaining theorem isolates the canonical compositor's action on iterated
unit sections, for an arbitrary commutative square without open hypotheses.

## Proved and sorry left

Original item: two holes. Closed the body of
`AlgebraicGeometry.ProEtale.StrictTower.openBetaRestriction_normalized` by a
complete Lean proof from the new lemma. The original
`AlgebraicGeometry.ProEtale.StrictTower.openBetaFiniteCompatibility` remains
`sorry`, unchanged.

Added one hole:
`AlgebraicGeometry.ProEtale.StrictTower.towerSquare_unit_sections`, node
`lem-cbc-tower-square-unit-sections`. Its proof is exactly `by sorry`, and its
module and node give the source and full argument in words. This is one
**decomposition**, not net hole reduction: one original hole closed, one new hole
added, two holes remaining in the packet. No definition contains `sorry`.

The complete packet compiled with `lcompile.py --all` (4.9 and 57.4 seconds).
Subsequent experiments exposed repeated categorical instance conversions; the
existing open-unit isomorphism calculation now shares one private helper and the
redundant category-to-quiver instance is disabled locally. The revised item
compiled in 55.9 seconds. No profiler options remain. Earlier attempts to prove
the smaller compositor-unit lemma and the finite coefficient cube are not part
of the delivery; the source-specific unit-section equation remains isolated.

## No longer needed

No existing import or module is withdrawn. The new proof import is private.
For the completed section calculation, the localized-ringed comparison route
is unnecessary: `lem-weil-proetale-weakly-etale-localization`,
`lem-weil-pbc-localize-ringed-site-morphism`,
`lem-sfb-proetale-open-restriction-counit`, and
`lem-pe-constant-left-module-inverse-image` are removed from the relevant proof
edges. Their declarations remain intact for other consumers. The finite hole's
original dependencies and proof plan remain.

## Where the brief, the DAG or earlier work was wrong

The helper node already attaches to the theorem in the item module; importing
that helper would be a self-import. Its section formula can instead be reduced
to the canonical unit-section equation without scalar transport of a separate
localization comparison. The new lemma has no open-immersion hypothesis and does
not assert exchange invertibility, restriction normalization, or finite
compatibility; these distinguish it from the parent statement.

Direct conversion of separately elaborated module/site expressions repeatedly
expanded large pullback and coefficient constructions. Sharing explicit
`towerUnitSection` and `towerSiteSquare` definitions permits the parent proof to
compile. This does not change the mathematical statement. The new equation was
checked for the identity-square specialization and its orientation agrees with
the inverse site-square map and contravariant restriction.

## New nodes

`lem-cbc-tower-square-unit-sections`, in
`Sheaf.AlgebraicGeometry.TowerSquareUnitSections`: the canonical inverse-image
compositor square preserves iterated adjunction-unit sections after restriction
along the inverse site-square isomorphism. Source: Stacks Tags 04J0 and 07A7,
with the conjugate-unit identity. The owning and helper nodes record the actual
reduction. No definition or consumer adaptation is required.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
