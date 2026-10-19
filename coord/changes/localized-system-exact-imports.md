# Import boundary of LocalizedModuleExactForSystems

## Reason

The item now contains its independent-universe direct-sum construction and proof,
so the previous public re-export of the restricted-universe interface is unused.
Imports needed only while elaborating the proof are ordinary imports. The public
imports required by the declarations and existing consumers remain public. No
declaration signature, definition, target statement, or mathematical hypothesis
changes.

## Old

```lean
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint
```

## New

```lean
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
```

The removed `LocalizedModuleExactIndependent`, `KFlat`, site restriction exactness,
abelian extension exactness, and abelian extension adjunction imports are not used.
The former proof-only dependencies are replaced by the direct construction and
generic Mathlib restriction adjunction in the item.

The public `RingObjects.Ab` import preserves `AddCommGrpCat.MonoidalCategory`
tensor declarations used by `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`,
which previously reached them through the removed broad interface.

## Users

Only the public import boundary changes; all declaration signatures and all
public definition bodies stay identical. No consumer is adapted. The table lists
the direct importers at this check; downstream users retain the same mathematical
API. Three consumer modules were compiled against the sandbox overlay as recorded
in report.md. The global build remains the check of all transitive consumers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.ProperBaseChange.SingletonSiteModuleComparison | unclaimed | retains abelian tensor API; no adaptation |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatFinitePresentationRetract | unclaimed | same signatures; no adaptation |
| Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat | unclaimed | same signatures; no adaptation |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical | Q6 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | A6 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleInjectiveFiniteCechRows | unclaimed | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleLocalDualInterval | unclaimed | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | H1 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction | unclaimed | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization | J6 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZero | U5 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleOpenTensor | G5 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal | U7 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | Y7 | same signatures; no adaptation |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | K9 | same signatures; no adaptation |
| Sheaf.CategoryTheory.CoefficientBidualTriangles | unclaimed | same signatures; no adaptation |
| Sheaf.CategoryTheory.RingedCechKoszulDualLimit | C1 | same signatures; no adaptation |
| Sheaf.CategoryTheory.RingedSiteDualityMaps | M5 | same signatures; no adaptation |
| Sheaf.CategoryTheory.RingedSitePerfectDuality | K3 | same signatures; no adaptation |
| Sheaf.CategoryTheory.RingedToposBinaryDescent | unclaimed | same signatures; no adaptation |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | M7 | same signatures; no adaptation |
| Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.AdicPullbackPresentationTransport | M9 | same signatures; no adaptation |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.CompactSupportReductionTower | F8 | same signatures; no adaptation |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.CompletedOpenExchangeTransport | R1 | same signatures; no adaptation |
| Sheaf.Paper.CompletedPullbackAdjunction | M2 | same signatures; no adaptation |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.DeltaRestriction | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.EtaleSupportAisleGenerators | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | P9 | same signatures; no adaptation |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | same signatures; no adaptation |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | R9 | same signatures; no adaptation |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | M3 | same signatures; no adaptation |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.OpenImmersionTensorPiece | Q3 | same signatures; no adaptation |
| Sheaf.Paper.ProperHeartBoundLattice | G2 | same signatures; no adaptation |
| Sheaf.Paper.ProperOpenTowerComparison | Q4 | same signatures; no adaptation |
| Sheaf.Paper.PurTwistSheafLocallyFree | K7 | same signatures; no adaptation |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.RingedDerivedSliceLocalization | Q7 | same signatures; no adaptation |
| Sheaf.Paper.RingedModelCurryingCoherence | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.RingedRefinementCoefficientSquare | D2 | same signatures; no adaptation |
| Sheaf.Paper.SectionDerivedRealization | T8 | same signatures; no adaptation |
| Sheaf.Paper.SectionDerivedTensorData | U6 | same signatures; no adaptation |
| Sheaf.Paper.SemilinearDerivedCalculus | T7 | same signatures; no adaptation |
| Sheaf.Paper.SemilinearDerivedSections | Q8 | same signatures; no adaptation |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.SiteBoundedConstantGradedModel | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.SiteBoundedTruncationModels | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.SiteTensorLocalModelComparison | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.SupportedCohomologyHom | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.TorsionLimitSheafCompleteness | B7 | same signatures; no adaptation |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | same signatures; no adaptation |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | same signatures; no adaptation |
| Sheaf.SecSmoothPurity.LocalizedExtensionZeroLinearDerived | Z7 | same signatures; no adaptation |
| Sheaf.SixFunctors.EtaleOpenTensor | E6 | same signatures; no adaptation |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | same signatures; no adaptation |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | same signatures; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | same signatures; no adaptation |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | same signatures; no adaptation |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | same signatures; no adaptation |
| Sheaf.SixFunctors.OpenTensorNormalization | V6 | same signatures; no adaptation |
| Sheaf.Targets.SliceRestrictionStrictDerivedLimit | S4 | same signatures; no adaptation |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | same signatures; no adaptation |

## Status

landed 20261019T005305-L-2748917 2026-10-19 (merge of deliver/J2/Sheaf.CategoryTheory.LocalizedModuleExactForSystems)
