## What changed

Proved `AlgebraicGeometry.Scheme.cbcIntegralCompactSupport_uniformRestriction` in
`Sheaf.Paper.IntegralCompactSupportUniformRestriction`, preserving all existing public
signatures and all three public constructions. Added proved private helpers for completed
coefficient normalization and scalar sections, finite locally closed stratification extension,
open-extension preservation over the actual coefficient ring, and adjoint-unique comparison
of the chosen open extension with `cbcDerivedOpenShriek`.

The existing public definitions and theorem statement were compared textually with the
shared source and remain verbatim.

Object preservation follows the compactification route: establish ambient geometry; append
the closed complement with zero perfect model; use the actual-universe local-perfect
criterion; apply actual-coefficient proper preservation to an identity Cartesian square.
The generic proved `pbcCompletedSection_directImage` helper is reused from
`PbcScalarExtension` through a private import, after normalizing coefficient maps.
Addition, scalar multiplication and distinguished triangles follow from the concrete
adjunctions and derived functor instances. The node proof and proof dependencies now record
this route. No definitions or statements were repaired and no consumers require adaptation.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.cbcIntegralCompactSupport_uniformRestriction`
(node `lem-cbc-integral-compact-support-uniform-restriction`).
Holes closed: 1. Holes added: 0. Holes remaining in the delivery: 0. Split off: 0.
The full proof compiled on the project server in 28.3 seconds before the final reuse
of the existing generic scalar-section helper; final packet verification is recorded by
the delivery tool.

The proof uses existing declared dependencies, including
`integralPadicLocalPerfectCriterion` and the reduction-control dependency of
`AdicCoefficientDatum.constructible_preservation`; their pre-existing holes are unchanged.

## No longer needed

Removed these direct proof imports (some remain transitive dependencies of the retained
library interfaces; this delivery does not withdraw any module):

- `WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover`
- `WeilConjectures.AlgebraicGeometry.Dimension`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.CompletedTowerDirectImage`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.Algebra.Category.ModuleCat.Ulift`
- `Mathlib.RingTheory.KrullDimension.Polynomial`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `WeilConjectures.Topology.Stratification`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.PbcUniformCompleteTriangulated`
- `Sheaf.Paper.PreservationConstructible`
- `Sheaf.Paper.SbcCompletedOperations`
- `Sheaf.SecSmoothPurity.LocalizedExtensionZeroLinearDerived`

The updated argument no longer needs separate proof steps invoking these former
proof-plan nodes (the defining category and direct-image constructions remain statement
dependencies, and several other nodes remain transitive dependencies):

- `lem-weil-valued-dvr-finite-quotients`
- `lem-weil-pbc-integral-stratified-perfect-characterization`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-closed-subset-closed-subscheme`
- `def-weil-pbc-bounded-constructible-complete`
- `lem-weil-pbc-standard-quotients-perfect`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `lem-sf-derived-homology-long-exact`
- `prop-weil-pbc-preservation-constructible`
- `lem-cbc-localized-extension-zero-linear-derived`
- `lem-weil-pbc-profinite-coefficient-inverse-image`
- `prop-weil-pbc-direct-image-limits`
- `lem-sbc-completed-operations-linear-natural-exchange`

The actual-coefficient local-perfect criterion replaces the lifted-ring stratified-perfect
characterization. Its reverse implication supplies the full uniform category directly,
so a separate explicit two-term reduction-interval argument is unnecessary here.
Actual-coefficient constructible preservation replaces the lifted-ring preservation
interface. Linearity follows from scalar sections and adjunctions, so the specialized
localized-extension and completed-exchange linearity theorems are unnecessary for this
proof. The generic closed-restriction zero proof and scalar-restriction comparison are
reused from the extension-zero modules through private proof imports; those modules remain
needed. No whole module is withdrawn or claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned characterization and proper-preservation convenience interfaces use
`E : Type u` and the lifted valuation ring, while this statement uses `E : Type (u+1)`
and its actual valuation ring. Applying those signatures verbatim would not typecheck.
Existing `IntegralPadicLocalPerfectCriterion` and `CompletedConstructiblePreservation`
provide the required actual-universe interfaces. The unit's compactification route is
preserved. Empty open or closed strata and zero complexes are covered by the explicit
zero model and finite-stratification construction.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
