## What changed

Filled two proof bodies in `Sheaf.Paper.CompleteProetaleStrictTowerRealization`.

`cbcRealizationSingleBeta_isIso` now proves invertibility for arbitrary commutative
constant coefficients, using the existing fixed-module equivalence and Cartesian
open comparison in `StrictTowerProperOpenArrows`. Fully faithful open extension
makes the relevant counit invertible. The displayed unit transpose is the
composite of that counit with invertible maps, so it is the specified mate itself
that is proved invertible. This includes the empty open and imposes no finiteness
condition on A.

`completeProetaleStrictTowerRealization_naturality` assembles the specified
reduction/open, scalar/open, projection, scalar/limit, pullback, direct-image/limit
and scalar/direct-image comparisons into two natural isomorphisms. Their
components are definitionally the existing source and target presentations.
Their naturality equations prove both conjuncts without comparing evaluations.

Added a proof-only `import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`
to reuse its proved private comparison helpers. Removed redundant proof-only
imports listed below. All public imports, declaration signatures, definition
bodies and original docstrings are preserved. No new declarations or nodes.

The server compiled the module after these changes. Explicit axiom inspection
of both filled declarations reports propext, Classical.choice, Quot.sound and
inherited sorryAx: these are proofs from existing project declarations, not a
claim that their entire dependency closure is already sorry-free.

## Proved and sorry left

Closed 2 of the original 9 holes; added 0 holes and split off 0 statements:

- `AlgebraicGeometry.Scheme.cbcRealizationSingleBeta_isIso`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_naturality`.

The following 7 holes remain unchanged, all attached to
`lem-cbc-complete-proetale-strict-tower-realization`:

- `AlgebraicGeometry.Scheme.cbcRealizationLimitMap_isIso`.
- `AlgebraicGeometry.Scheme.cbcRealizationReductionInv_properties`.
- `AlgebraicGeometry.Scheme.cbcRealizationScalarOpenInv_isIso`.
- `AlgebraicGeometry.Scheme.cbcRealizationProducts`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_evaluation`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_open`.

This is a partial delivery for a module with several holes, as allowed by the
worker brief. The main realization identity, its open-factor normalization and
its evaluation clause are not claimed proved.

## No longer needed

Removed the following direct proof-only imports, since the remaining public
imports and the explicit private-helper import suffice to compile the existing
declarations and the two proofs:

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.Paper.CompletedBaseChangeMap`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`.
- `Sheaf.Paper.PbcActualStrictPullback`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Sheaf.Paper.KoszulReconstruction`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.

No module or DAG node is withdrawn. The remaining seven holes still retain their
original proof plans and dependencies, including those accessible transitively;
these import removals do not assert that their underlying mathematics is unnecessary.
The two new proofs implement the existing open-unit and naturality arguments,
so no DAG route or unit route is changed.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The existing public `singleBetaInv_isIso` in
`FiniteOpenBaseChangeNormalized` requires finite coefficients, so it cannot prove
this item's arbitrary-A assertion directly. The general-coefficient comparison
already constructed privately in `StrictTowerProperOpenArrows` supplies the
required essential-image argument instead. No finite-A assumption was added.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
