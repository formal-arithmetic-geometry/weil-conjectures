## What changed

Completed four auxiliary proofs in `Sheaf.Paper.CompleteProetaleStrictTowerRealization`,
without changing any existing statement, definition, public import, or target.

- `cbcRealizationScalarOpenInv_isIso`: compare the recorded and geometric open
  adjunctions, use the proved generic scalar/open comparison to identify the open
  essential image, and prove the specified mate invertible using its unit/counit formula.
- `cbcRealizationProducts`: reflect scalar-restriction products through additive
  sheaves; transport open extension to the slice and use the proved canonical product
  comparison. Transfer the lifted countable indexing shape back to natural numbers.
- `cbcRealizationSingleBeta_isIso`: apply the existing arbitrary-coefficient theorem
  `openBetaModule_isIso`.
- `completeProetaleStrictTowerRealization_naturality`: assemble the source and target
  presentations as private natural isomorphisms and apply their naturality equations.

Private proof imports supply the slice presentation, open products, scalar/slice-extension
comparison, localized open unit, and arbitrary-coefficient open mate. Updated the node's
proof and dependencies to record these auxiliary routes. No consumer adaptation is needed.

## Proved and sorry left

Original holes: 9. Closed: 4, by the four declaration names above. Added: 0. Split off: 0.
This is a partial proof delivery, not a proof of the main realization theorem.

Five original holes remain, all attached to
`lem-cbc-complete-proetale-strict-tower-realization`:

- `cbcRealizationLimitMap_isIso`.
- `cbcRealizationReductionInv_properties`.
- `completeProetaleStrictTowerRealization`.
- `completeProetaleStrictTowerRealization_evaluation`.
- `completeProetaleStrictTowerRealization_open`.

The naturality proof uses the existing reduction/open properties theorem; this is a
proof from the stated dependency, and does not close that dependency's hole.

## No longer needed

Removed these redundant private imports; the remaining definitions have their existing
public dependencies and the completed proofs use the imports listed above:

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

No module is withdrawn, and no DAG dependency of the five unfinished proofs is pruned.
In particular the original proper/open normalization route remains needed.

## Where the brief, the DAG or earlier work was wrong

The item has nine original holes (the initial progress update's count of ten was wrong).
The single-level open mate already has a proved arbitrary-coefficient version in
`TowerOpenBetaNormalization`; the finite-coefficient theorem is unnecessarily restrictive
for this helper.

The declared dependency `CompletedOpenStrictMateIdentification` imports this module for
its endpoint definitions. It cannot be imported back here without first moving the common
interface to a dependency module and adapting that consumer. Its current holder is F3;
this delivery preserves its attachment and dependency and does not edit its file.
The scalar/open proof also distinguishes the separately recorded completed extension
from the generic geometric extension using the uniqueness of left adjoints.

Validation: the cleaned single-file compile passed in 36.5 seconds without warnings.
The required delivery command runs the server preflight and records its result.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
