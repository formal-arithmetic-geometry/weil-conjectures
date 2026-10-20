## What changed

Proved `AlgebraicGeometry.Etale.geometricPoint_derivedSections_adjunction` with its original
statement. The first clause follows from the counit
characterization of the unique right-adjoint comparison. For the second clause, identified
the actual section-to-germ map with the ordinary right-adjoint comparison, computed the
ordinary pushforward/sections normalization, and transported that calculation through the
canonical single-object augmentations and zeroth homology.

Added six proved generic helper modules under `Sheaf.CategoryTheory`: `AdjunctionComparisonSquare`,
`SectionsAdjunctionComparison`, `RightDerivedSingleH0`, `RightDerivedSingleCounit`,
`DerivedSingleConstantsComparison`, and `SingleAdjunctionComparison`. The augmentation module
generalizes the private proof in the source library's `CanonicalDirectImageH0Unit`; the single
comparison module reuses the private calculations in `DerivedRestrictionZeroTransport`.
The source library is unchanged. `singleRightDerivedUnit` is an explicit composite of existing
canonical maps, and contains no deferred data. All new public declarations have nodes.

Updated the item's proof route and recorded all six helper nodes. The unit statement and
unit proof route are preserved. Refactored the existing canonical derived comparison and two H⁰ isomorphism bodies through
new generic named constructions with definitionally identical values. The change record is
`coord/changes/M7-geometric-point-h0-normalization-api.md`. Existing signatures and public
imports are preserved, and one public import supplies the new constructions. Neither direct
consumer mentions the H⁰ names. `GeometricPointProjectionComparison` uses the derived
comparison with the same signature and value; no consumer adaptation is needed.

Validation: server compilation through `lcompile.py`; the cleaned item compiled in 24.6 seconds
with no temporary heartbeat or opacity settings. The final full sandbox check passed without warnings: all seven delivery modules and both
unchanged downstream consumers compiled. The item took 26.8 seconds,
`GeometricPointPullbackTensorNormalization` 6.1 seconds, and
`GeometricPointProjectionComparison` 7.7 seconds. The unchanged consumer copies were removed
after this check; they are not part of the delivery. The delivery tool records the final
preflight. The generic arguments use no nonzero,
boundedness, properness, torsion, or finiteness assumption. They apply to zero sheaves and to
the empty scheme.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.geometricPoint_derivedSections_adjunction`.

Added zero holes. No `sorry` remains in the item or in any new helper module. This is a proof,
not a decomposition into unfinished statements. The following new theorems are fully proved:

- `CategoryTheory.Adjunction.rightAdjointUniq_square`.
- `CategoryTheory.Adjunction.sections_comparison`.
- `CategoryTheory.Functor.singleRightDerivedH0Iso_def`.
- `CategoryTheory.Functor.rightDerivedFunctorUnit_homology_zero`.
- `CategoryTheory.Functor.rightDerivedFunctorUnit_homology_zero_after_exact`.
- `CategoryTheory.Functor.mapSingleRightDerivedH0Iso_conjugate`.
- `CategoryTheory.Adjunction.single_rightDerived_counit`.
- `CategoryTheory.Adjunction.single_mapDerivedCategory_counit`.
- `CategoryTheory.Functor.derived_single_constants_comparison`.
- `CategoryTheory.Adjunction.single_adjunction_comparison`.
- `CategoryTheory.Adjunction.single_adjunction_comparison_h0`.
- `CategoryTheory.Adjunction.normalizedDerivedRightAdjointIso_counit`.
- `CategoryTheory.Adjunction.normalizedDerivedRightAdjointIso_h0`.

Existing dependency holes, including `nonempty_geometricPointDerivedConstantsData`, are
imported unchanged as intended by the stage-3 dependency policy.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`.
- `Mathlib.CategoryTheory.Adjunction.Limits`.
- `Mathlib.CategoryTheory.Adjunction.Unique`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The point calculation explicitly imports
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`.
The new generic modules expose the other APIs the proof uses.

The item no longer has proof edges to `prop-weil-pbc-kinjective-resolutions-exist`,
`lem-weil-pbc-kinjective-hom-derived`, or
`lem-weil-pbc-right-adjoint-preserves-kinjective`: the proof uses the canonical derived
counit and single augmentations directly. Removed the obsolete `tool_uses` entries for the
first and third of those nodes. The ordinary termwise homotopy adjunction remains used by
the generic counit lemma; its approval is retained. The classical degree-zero and
bounded-below injective lemmas remain dependencies of the generic augmentation calculation.
No existing module or declaration is withdrawn, and no source-library dependency is claimed
globally unused.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The planned unbounded representative calculation
can be replaced by counit-compatible single-object squares. The existing source theorem
`exact_derivedAdjunction_single_counit` assumes an exact right adjoint and normalizes another
canonical derived adjunction; the image and sections right adjoints here are only left exact.
The new counit theorem handles the actual left-derived/exact-left transport used in this item.
The existing source augmentation theorem is specialized to a ringed-space direct image, so
its private resolution calculation was generalized to an arbitrary left exact additive functor.

The generic statements use named canonical `singleRightDerivedUnit`,
`singleRightDerivedH0Iso`, `mapSingleRightDerivedH0Iso`, and `normalizedDerivedRightAdjointIso`,
so the concrete applications share these canonical constructions. The definition refactor is recorded above; it leaves
the actual composites unchanged. Their conjugation API computes the normalized H⁰ map
from an augmentation-compatible square, using naturality of the single/homology isomorphism. The derived comparison API supplies its composed counit and H⁰ normalization, without
unfolding the actual stalk colimit. No compile limit or launcher tool was changed.

## New nodes

`lem-kun-adjunction-comparison-square` records compatibility of right-adjoint uniqueness
with arbitrary counit-compatible squares. Its theorem is proved in
`Sheaf.CategoryTheory.AdjunctionComparisonSquare`.

`lem-kun-sections-adjunction-comparison` records the ordinary sections/evaluation and
composite-adjunction normalization, proved in `Sheaf.CategoryTheory.SectionsAdjunctionComparison`.

`lem-kun-right-derived-single-h0` records the canonical augmentation and its H⁰ normalization,
including exact postcomposition, proved in `Sheaf.CategoryTheory.RightDerivedSingleH0`.
It also records the three explicit constructions used by these theorems and the proved
unfolding equation for the ordinary H⁰ isomorphism. Its conjugation theorem provides the
normalization API for augmentation-compatible squares. The definition-refactor record is
`coord/changes/M7-geometric-point-h0-normalization-api.md`.

`lem-kun-right-derived-single-counit` records the canonical transported derived counit on
single augmentations, including the exact-right specialization, proved in
`Sheaf.CategoryTheory.RightDerivedSingleCounit`.

`lem-kun-derived-single-constants-comparison` records compatibility of descended exact
composition and natural isomorphisms with single complexes, proved in
`Sheaf.CategoryTheory.DerivedSingleConstantsComparison`.

`lem-kun-single-adjunction-comparison` combines the normalized counit squares to identify
the derived right-adjoint comparison on single augmentations, proved in
`Sheaf.CategoryTheory.SingleAdjunctionComparison`. It includes its normalized H⁰
consequence and the actual canonical derived comparison construction, with proved
counit and H⁰ APIs.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
