# Sheaf.Paper.FiniteFreeCompletedScalarComparison proof elaboration commands

## Reason

The proof needs independent site and coefficient universes. High-priority equal-universe
sheafification instances otherwise select the wrong category. Local irreducibility and
explicit private projection/counit lemmas prevent repeated expansion of chosen derived
functors and limit constructions. Additional private helper universes and the Preadditive
namespace support the generic cochain model. These changes are recorded because the
interface checker conservatively treats all command changes as interface changes.

All four original public imports, all 20 original public statement texts and definition
bodies remain unchanged. No target or definition acquires a different mathematical meaning.
No public declaration is removed or replaced. The proof-only imports are listed in report.md.
The local transparency attributes and module-local options govern elaboration of this file;
they do not replace any public construction by a private helper.

## Old

Original non-declaration commands, verbatim as extracted by the interface checker:

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
```

## New

New non-declaration commands, verbatim as extracted by the same checker:

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open scoped ChangeOfRings
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
attribute [local irreducible] limit
attribute [local irreducible] completedScalarChangeData integralScalarReductionWitness
attribute [local irreducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
attribute [local semireducible] limit
attribute [local irreducible] limit
attribute [local irreducible] completedScalarChainComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] completedCoefficientMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] completedScalarComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] completedScalarIdentityMultiplication
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] completedScalarIdentityUnit
```

The additional `a b` universes belong only to private generic helpers. All original public
binders, universes, signatures, visibility and definition data stay verbatim. The source
library is unchanged. No downstream theorem statement becomes weaker, stronger or different.

## Users

There are 58 current direct importers and 1,317 transitive importers. The checker reports
only the command marker, with no changed public declaration name. Every direct importer is
listed below with its current claim holder. No consumer adaptation is necessary because
public imports, signatures and construction data are preserved. The new private helpers
are absent from consumer interfaces. The maintainer's global build remains the independent
check of downstream elaboration.

| Module | Current holder | Effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.AdicHeartPullbackFibres` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportArrowScalarTransport` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.CompletedIntegralScalarData` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.CompletedLineTensorCoherence` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.CompletedScalarChainShift` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.CompletedScalarShift` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.FdCoefficientComparison` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | A5 | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistDerivedScalar` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | E9 | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismScalarTensorKFlatModel` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.PerAdicCommonStageTruncations` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.PointSectionsScalarExtension` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.PurAdicScalarExtensionTorBound` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.PurShiftedTateUnitScalarCoherence` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | G7 | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.RoosIntrinsicUnitComparison` | H6 | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.ScalarCompletionAssociator` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.ScalarPullbackStrictConeNaturality` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.SpecifiedHomScalarEvaluation` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | Public statements and construction data unchanged; no adaptation. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | H7 | Public statements and construction data unchanged; no adaptation. |

## Status

landed 20261022T013407-L-3561985 2026-10-22 (merge of deliver/F1/Sheaf.Paper.FiniteFreeCompletedScalarComparison)
