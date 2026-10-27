## What changed

Proved `WeilConjectures.PurScalarProjection.projection_unit` in the assigned module.
The published `PurProjectionData.integralDomains` already asserts that the source
completion unit is invertible. Unfolding the published `integralMap` cancels that
unit against its inverse and gives exactly the prescribed ordinary projection
followed by compact support of the inner unit. Cancellation of this same unit
then proves uniqueness. No completion comparison or projection map is changed.

Removed eighteen unused private proof imports. Kept all public imports and every
existing declaration signature and docstring. A theorem-local unused-section-variable
linter setting retains the original separatedness binders; those hypotheses are
unneeded by this particular proof and were not removed.

Validation: the full assigned module compiles on the server in 21.1 seconds without
warnings, after removing the unused private imports. No local Lean or Lake command
was used. Searches included LeanFinder, Loogle, the provided grep service and direct
source searches. Loogle located `CategoryTheory.IsIso.hom_inv_id`; its associated
cancellation simp lemma proves the normalization directly.

## Proved and sorry left

Closed 1 existing hole, added 0 holes, split off 0 statements:
`WeilConjectures.PurScalarProjection.projection_unit`.

The following 10 original holes remain unchanged, all belonging to
`lem-pur-compact-support-scalar-projection-identification` and retaining their
existing source and complete natural-language proof docstrings:

- `WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique`
- `WeilConjectures.PurScalarProjection.properProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.openProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.realization_existsUnique`
- `WeilConjectures.PurScalarProjection.native_scalar_identification`
- `WeilConjectures.PurScalarProjection.gamma_identification`
- `WeilConjectures.PurScalarProjection.diagram_projection`
- `WeilConjectures.PurScalarProjection.inner_domain`
- `WeilConjectures.PurScalarProjection.ordinaryCompletedSquare`
- `WeilConjectures.PurScalarProjection.compactSupportScalarProjectionIdentification`

This is a partial delivery of a module with several holes. The normalization and
uniqueness proof uses the existing typing theorem, which remains a separate item;
no claim is made that its transitive axioms are already sorry-free.

## No longer needed

The completed `projection_unit` proof does not need the following private imports,
which were removed from this module:

- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.CompletedTensorUnitInsertion`
- `Sheaf.Paper.CompletedPullbackAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Paper.CompletedOperationTowerSubstitution`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientTensorCtf`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedCoefficientPushforwardComparison`
- `Sheaf.Paper.CompletedOpenExchangeTransport`
- `Sheaf.Paper.CompletedOpenTensorSystemRealization`
- `Sheaf.Paper.PerfectQuotientExchangeNormalization`
- `Sheaf.CategoryTheory.TowerLimitTransposeNormalization`
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`
- `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Mathlib.CategoryTheory.Adjunction.Mates`

No node or module is withdrawn. The original nine-step DAG plan and its dependencies
remain relevant to the ten untouched holes, so their proof dependencies and unit
route are retained. Removing these direct unused imports does not claim that their
mathematics is unnecessary for the unfinished proof or that transitive imports vanish.

## Where the brief, the DAG or earlier work was wrong

The local proof plan for `projection_unit` is longer than necessary for its stated
constructible domain: `integralDomains` gives an invertible source unit, and
`integralMap` is explicitly its inverse followed by the asserted ordinary arrow.
Thus this normalization and uniqueness need no additional completion-reflector
argument. The other signatures are unchanged.

The existing `PurCompactSupport.comparison_projection` cannot be used as a shortcut
for this item's scalar square: its owning node
`lem-pur-compact-support-integral-coefficient-comparison` explicitly depends on this
item. That circular route was excluded. No false statement or tool fault was found.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
