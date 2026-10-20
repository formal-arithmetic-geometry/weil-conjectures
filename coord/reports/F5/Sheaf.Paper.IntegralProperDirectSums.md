## What changed

Retained and checked the interrupted sandbox against the current library. Proved
`AlgebraicGeometry.ProEtale.integralProperDirectSums` without changing its signature or
`IntegralProperDirectImageAssertions`. The proof establishes the actual two truncation
arrows, constructs the coproduct comparison via a naturality square after lower truncation,
and proves preservation of the localizing closure by its intersection universal property.
`integralIndConstructibleStability` is also proved, from abelian heart closure, derived
cohomology/sum compatibility, and the definition of localizingClosure.

Removed the duplicated lower-truncation argument from the finite-window helper:
it now applies the already proved `lowerWindowOfBounds`. Updated the theorem docstring
to the actual four-step proof. Added the declared integral heart/continuity interfaces
to the estimate and heart-closure modules, and removed their unused five-lemma import.

The existing common-lower-bound coproduct theorem replaces finite-interval induction.
The localizing predicate quantifies over the larger object universe; the proof shrinks
an existing coproduct to its nonzero support using its orthogonal idempotents. This
covers empty families and avoids assuming large coproduct existence.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.integralProperDirectSums`
(`det-prop-int-compactness-direct-sums`), 1 of 1 original holes.
New proved theorems:
- `AlgebraicGeometry.ProEtale.integralIndConstructibleStability`
  (`lem-sfb-integral-ind-derived-stability`).
- `AlgebraicGeometry.ProEtale.integralIndConstructibleHeartClosure`
  (`lem-sfb-integral-ind-heart-closure`), using integral Hom/Ext continuity, the canonical
  constructible presentation, ambient kernel/cokernel calculations, extension descent
  and finite-subsum presentations.
All private helpers in the delivered modules are proved.

Further proved theorems:
- `AlgebraicGeometry.ProEtale.integralProperCohomologicalBounds`
  (`lem-sfb-integral-proper-cohomological-bounds`), by integral coefficient transport,
  the constructible heart estimate, filtered heart continuity and the generic
  hypercohomology/lower truncation arguments.
- `AlgebraicGeometry.ProEtale.integralProperConstructibleHeartBound`
  (`lem-sfb-integral-proper-constructible-heart-bound`), by the completion Roos triangle.
- `AlgebraicGeometry.ProEtale.integralProperReductionBound`
  (`lem-sfb-integral-proper-reduction-bound`), by the geometric torsion bound, coefficient
  forgetting and the declared finite cohomological-dimension amplitude theorem.
  The right t-exactness of reduction is proved by adjunction and orthogonality.

One new hole remains:
- `AlgebraicGeometry.ProEtale.integralProperReductionModel`
  (`lem-sfb-integral-proper-reduction-model`). This supplies classical etale models of
  finite integral reductions and their compatibility with ordinary proper image. It
  has no dimension bound, no integral reconstruction, no Ind-heart, window, coproduct,
  or localizing assertion. It is a separate comparison step of source proof (1).

This is a decomposition: 1 original upper hole closed, 1 lower comparison hole added,
net 0 holes in the delivered declarations. The added theorem is strictly a comparison
part of the argument. All amplitude estimates and categorical glue are proved from it.
No definition contains sorry or arbitrary data chosen from an unproved existence assertion.
The comparison witness is eliminated only inside a theorem proof.

## No longer needed

The main proof needs neither the finite-range induction nor its separate five-lemma
step (`lem-weil-pbc-five-lemma`, Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four).
No rational-coefficient proper-window theorem is used. Integral compactness's uniform
Ext-bound and compactness conclusions are unnecessary: structural Dic stability is
proved independently of any choice of Ext bounds. The existing public import of
IntegralConstructibleCompactness is retained to preserve the public interface.

The following proof-only imports were removed from the main module (the estimates module
imports the subset it needs): `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`, `Mathlib.CategoryTheory.Adjunction.Limits`,
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`,
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`,
`Sheaf.AlgebraicGeometry.DimensionAffineOpenCover`, `Sheaf.AlgebraicGeometry.DimensionBaseChange`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`,
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`,
`Sheaf.AlgebraicGeometry.ProEtaleLeftComplete`, `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`,
`Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage`,
`Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound`,
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`,
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound`,
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, `Sheaf.Paper.CartesianCoefficients`,
`Sheaf.Paper.CondensedModuleDerivedPushpull`, `Sheaf.Paper.DerivedNakayamaResolution`,
`Sheaf.Paper.IntegralCohomologicalAdicCriterion`, `Sheaf.Paper.IntegralConstructibleHeart`,
`Sheaf.Paper.IntegralProperBaseChange`,
`Sheaf.Paper.LocalizingClosureExistence`, `Sheaf.Paper.WeilCompletedTensorReflector`,
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`,
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.

The new estimate, heart-bound, abelian-closure and derived-stability modules also no longer
import `Sheaf.Paper.IntegralConstructibleCompactness`; their statements use the smaller
constructibility and coefficient interfaces. Derived stability imports the localizing
closure interface directly. The reduction-bound module no longer imports
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts`.
The reduction-model and reduction-bound modules use `CondensedConstantConstructibility`
in place of the compactness module from their initial drafts.

The geometric torsion argument uses the supplied geometric fibres directly, so
`lem-pc-dim-base-change` (`Sheaf.AlgebraicGeometry.DimensionBaseChange`) and
`lem-pc-dimension-affine-open-cover` (`Sheaf.AlgebraicGeometry.DimensionAffineOpenCover`)
are unnecessary for the entire new argument. `det-pe-milnor-sequence` is replaced by
the explicit augmented Roos triangle and its homology exact sequence.

The following old top-level `tool_uses` approvals are removed from the main node.
Some interfaces remain dependencies of its proved helper nodes; their removal here
records that they are no longer direct steps in the main module:

- `sk-def-sfb-module-pushforward-pullback`.
- `sk-prop-sfb-cartesian-coefficients`.
- `sk-def-sfb-module-derived-pushpull`.
- `lem-weil-pbc-right-adjoint-preserves-limits`.
- `lem-pc-right-derived-functor-triangulated`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`.
- `lem-weil-pbc-sheaf-tensor-closed`.
- `sk-def-sfb-derived-categories`.
- `lem-sfb-integral-cohomological-adic-criterion`.
- `det-prop-sfb-qlbar-colimit-x-integral-limit`.
- `lem-weil-pbc-finite-type-over-noetherian`.
- `det-pe-derived-nakayama-resolution`.
- `lem-weil-pbc-module-sheaves-colimits-forgetful`.
- `det-pe-classical-derived-equivalence`.
- `sk-prop-sf-comparison`.
- `lem-kun-proper-torsion-cd-bound`.
- `lem-pc-dim-base-change`.
- `lem-pc-dimension-affine-open-cover`.
- `def-kun-truncations`.
- `sk-thm-pe-direct-image-comparison`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
- `def-weil-derived-limit`.
- `det-pe-milnor-sequence`.
- `det-proper-heart-continuity-direct-image`.
- `lem-weil-proetale-countable-products-exact`.
- `lem-weil-derived-limit-products-core`.
- `det-pe-left-complete-iso`.
- `lem-weil-pbc-five-lemma`.
- `def-weil-abstract-derived-category`.
- `lem-weil-pbc-ringed-koszul-completion-reflector`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
- `def-weil-finite-type-morphism`.
- `lem-pc-separated-quasi-separated`.

The main node also drops these former direct proof dependencies, now handled by
its helper interfaces where needed: `det-prop-int-compactness-compact`, `det-thm-sfb-proper-base-change-integral`, `lem-sfb-left-complete-heart-upper-bound`, `sk-lem-int-integral-heart`.

## Where the brief, the DAG or earlier work was wrong

The original plan has a finite-range sum induction, but the landed ordinary qcqs
bounded-below coproduct theorem handles every family with a common lower bound. Only
the lower truncation is therefore needed to prove arbitrary coproduct preservation.
The two actual window arrows are still both proved. The structural part of the integral
compactness theorem cannot simply be applied: its signature additionally demands a
chosen uniform Ext-bound function, absent from this item's hypotheses. Its structural
argument is isolated rather than adding such a hypothesis.

No existing statement or definition has been changed. No forced consumer adaptation.
The existing rational Ind-heart results cannot be used for the integral coefficient:
`continuousMapRingObj E` and `padicIntegersRingObj` define different rings. The general
private arguments in `IndConstructibleExtensions` and `IndHeartKernelsCokernels` give
usable templates once degree-zero/one integral continuity is transported. The compactness
theorem cannot supply this without its extra uniform-Ext-bound hypothesis.

The retained sandbox's reference clock was reset during provider-error resumptions:
the retained history recorded start 1792426077.6677139, whereas the resumed metadata
records 1792434151.951863. The dispatcher also reinstated `.brief2` (citations), `.brief3`
(msearch), `.brief4` (duplicate check), and `.brief5` (worker delivery). I did not edit
these files or the clock. The first resumed dry run refused the then-unfinished packet
under the split-off reference rule. Work continued: the cohomological bounds and the
completion argument were completed, and the remaining task was narrowed to a finite
coefficient comparison. No push preceded this resumed work.

## New nodes

`lem-sfb-integral-proper-cohomological-bounds` records the proved proper heart and
bounded-above estimates; it excludes window maps, coproducts and localizing preservation.

`lem-sfb-integral-ind-heart-closure` records proved abelian integral Ind closure,
independently of proper maps, fibre dimensions, derived windows and compactness.

`lem-sfb-integral-ind-derived-stability` is proved. It promotes the preceding abelian
closure result to truncation and coproduct stability of Dic, and contains Loc(Dbc).

`lem-sfb-integral-proper-constructible-heart-bound` records the proved passage from
finite bounds to the integral constructible heart bound through the completion triangle.

`lem-sfb-integral-proper-reduction-bound` records the proved geometric torsion amplitude
step. It uses geometric stalks directly, so dimension invariance on affine charts is
unnecessary.

`lem-sfb-integral-proper-reduction-model` records the remaining comparison, sourced from
proof (1)'s classical reduction and discrete direct-image comparison. Its edge cases
include zero complexes, torsion input, n=0 (exponent one), and empty schemes. The positive
quotient is finite; its exact constant realization and bounded classical equivalence
give the two required isomorphisms. Right t-exactness is proved separately from the
derived extension/restriction adjunction, and exact faithful realization reflects
cohomological bounds. It is neither an integral-image estimate nor a restatement
of any original assertion.

No existing signature or definition changed, and no consumer adaptation or change record
is required.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
