## What changed

Retained and repaired the earlier sandbox adjunction proof in
`Sheaf.Paper.ProperOpenCoefficientRefinement`. The existing public definitions and theorem
signatures are unchanged. Added proved private helpers for the transported mate counit,
the open unit, the restriction transformation, bounded/unbounded normalization, and the
two categorical pasting/cancellation arguments. The top theorem is derived from these
helpers and the existing `properOpenIdentification_unit`.

Isolated the independent scalar/pullback composition result of Stacks 0D6D/03D8 as
`Sheaf.Paper.ScalarPullbackComposition`, node `lem-sf-scalar-pullback-composition`.
This is about arbitrary composable scheme maps and arbitrary coefficient maps; it has
no proper/open refinement, no compact support and no boundedness hypotheses. Its remaining
proof obligation is the representative-normalization composition calculation, not the
original refinement statement. The original node now records the categorical route.

## Proved and sorry left

Closed in the item: `AlgebraicGeometry.Etale.properOpenComparison_coefficient_refinement`
(node `lem-sf-proper-open-coefficient-refinement`). This is currently a decomposition:
one original hole closed, one genuinely separate coherence hole added, net zero.
The previously proved `properOpenCoefficientOpenInverse_isIso` remains proved.
No sorry remains in the item module or in a private helper or definition.

The delivery adds one sorry:
`AlgebraicGeometry.Etale.scalarPullback_composition`, in
`Sheaf.Paper.ScalarPullbackComposition`, node `lem-sf-scalar-pullback-composition`.
It is a genuinely separate general coherence result, with its complete K-flat representative argument recorded in the declaration docstring; the theorem remains the one split-off `sorry` in this delivery.
The existing dependency `AlgebraicGeometry.Etale.properOpenIdentification_unit` remains
an imported statement with its existing sorry; this delivery does not add that hole.

Validation: both delivered modules compile together. All six unchanged direct
consumers compile against the delivered parent overlay (5.8–25.7 seconds each).
The earlier dry run identified missing LeanSearch metadata and a public-import
change record; both are now supplied. The final direct dry run passed compilation,
the axiom probe and preflight at `f364cff986` (CODEX independent review).
The delivery contains one item hole closed and one separate coherence hole added;
it is a decomposition, not a net hole reduction.

## No longer needed

The proof now uses the already stated normalization of theta instead of redoing its
clopen-section construction, injective model and componentwise argument. The unit record
has empty realized statement and step lists, so no realized unit step is bypassed.

Removed imports:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.AlgebraicGeometry.ProperOpenSection`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.EtaleUnboundedRestrictionComparison`
- `Sheaf.AlgebraicGeometry.OpenSectionClopen`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

Removed direct proof dependencies and old tool approvals for the geometric clopen-product,
K-flat open-extension, tensor-descent, and injective-model calculations:
- `cor-cbc-derived-extension-zero-base-change`
- `def-kun-projection-formula-map`
- `def-weil-pbc-extension-by-zero`
- `lem-amb-etale-adjoint-locality`
- `lem-cbc-extension-zero-composition`
- `lem-cbc-proper-open-interchange-coherence`
- `lem-cbc-proper-support-sheaf-composition`
- `lem-pc-kflat-resolution`
- `lem-pur-derived-change-of-rings`
- `lem-weil-pbc-etale-sheaf-clopen-product`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-inverse-image-composition-module-linear`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-proper-open-section`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `prop-weil-pbc-inverse-image-modules-exact`

The scalar composition node retains the K-flat and ordinary inverse-image composition
results it needs. The existing proper/open normalization dependency retains its own
geometric dependencies. Pruning here does not assert those nodes are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had an unproved private coherence theorem and did not compile:
reducibility attributes on imported definitions were rejected, the transported counit
needed explicit functorial cancellation, and the bounded/unbounded unit calculation
needed explicit identity components. These are repaired without changing published data.
The original DAG's full clopen/injective computation is unnecessary once the existing
`properOpenIdentification_unit` is used. Composition coherence for the particular
K-flat-normalized `scalarPullbackIso` was not an existing Lean declaration: the general
ringed tensor/pullback theorem and module-linearity theorem do not themselves state this
normalized two-morphism square.

## New nodes

`lem-sf-scalar-pullback-composition`: the independent normalized scalar/pullback
composition lemma (Stacks 0D6D, 03D8 and 0G7E), recorded in its own module. It is strictly
one part of the argument: the item still proves the transported mate identity, theta
normalization and final open-adjunction cancellation. No existing definition or statement
was changed, and no forced consumer adaptation was needed. The public-import
pruning and its six consumer checks are recorded in
`coord/changes/proper-open-coefficient-refinement-public-imports.md`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
