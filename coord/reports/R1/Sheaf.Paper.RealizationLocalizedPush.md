## What changed

Replaced the hole in `WeilConjectures.realization_localized_push` by an explicit
construction of `RealizationLocalizedPushData`. The comparison is the adjunction
mate of the localization unit, so its naturality and normalization are proved
rather than chosen independently. Integral stability follows from the existing
`sfIntegralDirectImage_constructible` theorem and normalized coefficient transport.

Added five modules separating genuinely distinct pieces of the argument:
`ContinuousCoefficientGeneralPullbackIso`, `RealizationCoefficientSquare`,
`RealizationContinuousDirectImage`, `RealizationCompletedImage`, and
`RealizationScalarPushMate`. The first extends the existing proof of continuous
coefficient pullback beyond immersions. The square is checked on finite constant
sections and residue projections. Direct-image transport uses the specified
section normalization. Completed-image agreement preserves the actual finite
transition maps and compares their Roos triangles.

No existing declaration signature, public import, definition, or source-library
module was changed. All additions are under `Sheaf`; no forced adaptations.

## Proved and sorry left

Original hole: `WeilConjectures.realization_localized_push` (one).
The submitted main module contains no `sorry`: its construction and assembly are
complete relative to the named scalar-mate theorem below.

Proved additions: `AlgebraicGeometry.Scheme.continuousCoefficientPullback_isIso_of_finiteExtension`,
`WeilConjectures.realizationCoefficientSquare`,
`WeilConjectures.realizationContinuousDirectImage`, and
`WeilConjectures.realizationCompletedImage`, together with the proved value, residue,
and normalized-pullback APIs in the first module.

One new hole remains: `WeilConjectures.realizationScalarPushMate_isIso`, node
`lem-weil-pbc-realization-scalar-push-mate`. This is the scalar localization part
only, for arbitrary bounded-below complexes and qcqs maps. It asserts neither
coefficient-map existence, internal encoding compatibility, integral stability,
completed-image agreement, nor construction of a natural comparison. Its source
is Bhatt--Scholze Lemma 6.8.2 and Remark 6.8.15, with Hemo--Richarz--Scholbach
Lemma 5.3(1). Its docstring records the telescope proof and the common lower bound.

The delivery is a decomposition (one original hole closed, one new hole added),
not a net hole reduction. The other four new public results and all private
helpers have complete proofs. No holes occur in definitions or private helpers.

## No longer needed

Removed the following direct proof imports from the item:
`Sheaf.Paper.ContinuousIntegralLocalization`,
`Sheaf.Paper.ContinuousIntegralLocalizationHomology`,
`Sheaf.Paper.ContinuousIntegralLocalizationContinuity`,
`Sheaf.Paper.ContinuousChartSchemeNaturality`,
`Sheaf.Paper.ContinuousCoefficientRealizations`,
`Sheaf.Paper.ContinuousModuleEncodingScalarExtension`,
`Sheaf.Paper.ProfinitePointPullback`,
`Sheaf.Paper.CompletedDirectImageLimits`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, and
`Mathlib.Topology.Algebra.Valued.LocallyCompact`.

This does not withdraw those modules or upstream declarations. Telescope facts
remain in the scalar-mate node's mathematical proof dependencies. Continuous
realization facts used by the comparison modules remain dependencies there.
The general derived-product argument replaces the need to apply
`CompletedDirectImageLimits` to an incompatible strict-tower presentation.
K-injective resolutions and composition use the existing ambient APIs.
No claim of global pruning is made without a target-closure calculation.
Removed the parent node's direct tool-use approvals for
`lem-weil-l-adic-extension-integers-dvr` and
`prop-pur-kinjective-resolutions-exist`: these are no longer direct steps of the
parent proof; localization coefficient algebra belongs to the scalar-mate result,
and the other comparisons use the existing ambient K-injective APIs.

## Where the brief, the DAG or earlier work was wrong

The stated coefficient inverse-image interface was restricted to immersions,
while this item requires arbitrary finite-type morphisms. Its integral and
rational proof works for arbitrary scheme morphisms; the new general theorem
preserves the existing immersion interface unchanged.

The scalar telescope results are stated for internal condensed modules and a
small coefficient field, whereas this item uses the normalized sectionwise
coefficient model with a universe-polymorphic finite extension. They cannot be
applied by definitional simplification. The remaining scalar-mate node records
that separate localization argument with the actual coefficient comparisons.

A whole-DAG traversal also encounters pre-existing cycles below source dependency
nodes, including `lem-pc-ring-hom-extension-differential` and
`lemma-weil-pbc-derived-exchange-replacement`. The same cycles occur in the
unchanged repository before this packet; this delivery does not repair those
unrelated records. Lean import compilation succeeds.

The detailed completed coefficient model and the functions-sheaf model are
isomorphic, not interchangeable by rewriting. Their structural maps have been
compared through the prescribed finite quotient normalization.

## New nodes

`lem-weil-pbc-continuous-coefficient-general-pullback-isIso`: normalized continuous
integral and rational inverse-image maps are isomorphisms for arbitrary scheme
maps; includes the value and residue APIs needed by the square.

`lem-weil-pbc-realization-coefficient-square`: normalized integral and rational
coefficient maps commute with scheme pullback.

`lem-weil-pbc-realization-continuous-direct-image`: the internal/section module
encoding intertwines ordinary continuous derived direct image.

`lem-weil-pbc-realization-completed-image`: ordinary ambient direct image of a
complete detailed object agrees with the specified finite-image Roos limit,
with its actual transitions.

`lem-weil-pbc-realization-scalar-push-mate`: the normalized scalar mate is
invertible on bounded-below complexes for a qcqs morphism.

No definition or statement change records are needed.

Validation: all six modules compile through lcompile.py; only the named scalar-mate
theorem contains `sorry`. Edge cases checked in the mathematical argument include
empty schemes, zero complexes, identity maps, l-torsion complexes (both localized
vertices vanish), ramified coefficient extensions, and arbitrary cohomological
lower bounds. No properness or constructibility is used in the remaining lemma.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
