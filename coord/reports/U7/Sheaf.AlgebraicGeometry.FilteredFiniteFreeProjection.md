## What changed

Prove the three original holes in `Sheaf.AlgebraicGeometry.FilteredFiniteFreeProjection`:
projection naturality, finite-free normalization for every presentation, and filtered
finite-free projection with the actual cocone legs and strict bounded representatives.
The existing public statements remain unchanged. Three functor definitions are
refactored into equivalent compositions to avoid expensive elaboration of product
functor records. The objects, maps, tensor order, and actual projection are unchanged.

Add `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityCoefficientRestriction`, proving
bounded continuity for the specified R-linear direct image from the existing
natural-coefficient continuity theorem, exact restriction of scalars, and uniqueness
of right derived functors. This isolates a separate coefficient-action comparison
already required by step 6 of the original plan.

Restrict the existing native K-flat comparison to the flat representatives instead
of reconstructing its natural isomorphism. Use the explicit quotient-comparison
isomorphism to keep localization constructions abstract during elaboration. Compare
the supplied tensor models with the native localization tensor by restriction to
resolving representatives. Use the native one-K-flat comparison to obtain natural
strict models. Preserve the blueprint unit's finite-free and bounded-continuity route.

## Proved and sorry left

Original holes closed: `projection_naturality`, `finiteFreeNormalization`, and
`filteredFiniteFreeProjection` (all in namespace
`AlgebraicGeometry.Scheme.FilteredFiniteFreeProjection`). There are 3 original holes,
0 remaining holes, and 0 added holes. The final combined launcher compilation
passes without warnings: 0.8 seconds for the new coefficient-restriction theorem
and 31.3 seconds for the item. The delivery tool runs the required preflight.

The new `AlgebraicGeometry.Scheme.ProEt.boundedContinuityDirectImage_coefficients`
compiles with no sorry. No holes are added. The imported planned statements remain
the responsibility of their own nodes; this delivery does not replace their proofs.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.ProjectionMateExact`: mate naturality and unit invertibility follow
  directly from the specified comparison, the adjunction, and tensor-unit actions.
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`: use the independent
  coefficient tensor-colimit theorem and the existing complex bifunctor instances.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`: use the
  independent coefficient closed structure exposed by the native tensor infrastructure.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
- `Sheaf.Algebra.Homology.RingedToposPullbackFilteredColimits`: colimit preservation
  follows directly from the given module adjunction.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful` from the item:
  the new coefficient-restriction module uses this result privately.

The item no longer directly needs nodes `lem-weil-pbc-ringed-projection-mate-exact`,
`lem-pc-module-filtered-colimits-tensor`, `lem-pc-sheaf-modules-tensor-closed`,
`lem-weil-pbc-ringed-topos-pullback-filtered-colimits`,
`lem-sp-grothendieck-enough-injectives`, `lem-weil-pbc-dplus-injective-representative`,
and `lem-weil-pbc-derived-plus-iso-on-cohomology`. In particular the last three are
unnecessary because `DerivedCategory.isIso_iff` detects isomorphisms in the unbounded
derived category. No source-library declaration or module is withdrawn. The
forgetful-colimit node remains needed by the new continuity comparison.

Obsolete top-level tool approvals for these unused nodes are removed from the item's
node; remaining approvals retain their original order. No new approval is fabricated.

## Where the brief, the DAG or earlier work was wrong

The last proof step unnecessarily required bounded-below direct-image representatives
for cohomological detection: the unbounded detection theorem is already available.
The source cohomology comparison can also resolve the fixed tensor factor once, so
its proof requires no boundedness of the direct image and no flatness of the varying
coefficient. The original flatness hypotheses and public statement stay verbatim. The proof
retains the source-flatness hypothesis and uses the stated flatness of the
pulled-back colimit in the strict comparison.

The original plan's restriction-of-coefficients argument is a substantive natural
functor comparison. The added proved theorem records it explicitly, rather than
assuming the two differently defined derived direct images are definitionally equal.

## New nodes

`lem-pe-bounded-continuity-coefficient-restriction` in
`dag/nodes/sec-six-functors-basics/` realizes the coefficient-restriction part of step 6.
Its module proves that the comparison for any uniformly bounded filtered complex
diagram and any actual colimit cocone is invertible with the specified R-action.
The coefficient comparison is proved, so it adds no split-off hole. The definition
refactoring is documented in
`coord/changes/filtered-finite-free-functor-factorizations.md`. Downstream analysis
finds no consumer outside the item module for the three changed functor definitions.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
