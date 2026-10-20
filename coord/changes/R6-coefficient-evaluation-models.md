# Coefficient evaluation public interface

## Reason

The ordinary strict-system construction must be available to independent derived-adjunction,
level-comparison and tensor-coherence proofs without importing the theorem assembling them.
Move the existing definitions, instances, theorem proofs and generic package interfaces verbatim
into `Sheaf.Paper.CoefficientEvaluationModels`, and publicly import that module from the original
item. The original module still declares `coefficientEvaluationDerivedLeftAdjoint` with its
exact original signature. This is an interface-location change, not a mathematical definition
or statement change. No source-library module is modified.

## Old

The original item declared the 36 support declarations listed below directly, under these public
imports (verbatim):

```lean
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
```

## New

The original module re-exports the support declarations and their original public imports via:

```lean
public import Sheaf.Paper.CoefficientEvaluationModels
```

The moved support declarations retain their names, universes, signatures, attributes, bodies and
visibility. Their original module header and public imports are retained in Models. Proof-only
imports that the support declarations do not use are removed there; proof modules import their
own needed dependencies. The additional ordinary-extension interface and its proved existence
theorem are new declarations, not modifications of the moved interface.

- `SheafOfModules.coefficientQuotientSheaf`
- `SheafOfModules.coefficientQuotientMap`
- `SheafOfModules.coefficientLevelModules`
- `SheafOfModules.coefficientRestriction`
- `SheafOfModules.CoefficientSystem`
- `SheafOfModules.CoefficientSystem.Hom`
- `SheafOfModules.coefficientSystem_id_comm`
- `SheafOfModules.coefficientSystem_comp_comm`
- `SheafOfModules.CoefficientSystem.identity`
- `SheafOfModules.CoefficientSystem.Hom.compose`
- `SheafOfModules.coefficientSystem_category_laws`
- `SheafOfModules.coefficientSystemCategory`
- `SheafOfModules.coefficientEvaluation`
- `SheafOfModules.CoefficientSystem.AbelianNormalized`
- `SheafOfModules.coefficientSystem_abelian_exists`
- `SheafOfModules.coefficientSystemAbelian`
- `SheafOfModules.coefficientEvaluation_additive`
- `SheafOfModules.coefficientEvaluation_exact`
- `SheafOfModules.siteCoefficientTensor_map_id`
- `SheafOfModules.siteCoefficientTensor_map_comp`
- `SheafOfModules.siteCoefficientTensor`
- `SheafOfModules.siteCoefficientTensor_additive`
- `SheafOfModules.SiteCoefficientTensorAdjunctionNormalized`
- `SheafOfModules.siteCoefficientTensorAdj_exists`
- `SheafOfModules.siteCoefficientTensorAdj`
- `SheafOfModules.coefficientTensor`
- `SheafOfModules.coefficientTensorAdj`
- `SheafOfModules.siteScalarUnderlyingIso`
- `SheafOfModules.siteTensorUnitUnderlying`
- `SheafOfModules.coefficientTransitionUnderlying`
- `SheafOfModules.CoefficientTransitionsNormalized`
- `SheafOfModules.CoefficientTensorUnitNormalized`
- `SheafOfModules.CoefficientTensorAssocNormalized`
- `SheafOfModules.DerivedCoefficientScalarExtension`
- `SheafOfModules.CoefficientEvaluationExtensionData`
- `SheafOfModules.CoefficientEvaluationDerivedPackage`

Every definition used by a target is identical to its previous definition. No target meaning
changes and no target statement review is reopened by this relocation. The current and
quarantined consumer sources have been inspected for use of the moved API. The normalized
scalar units, underlying-sheaf identity comparisons and generic structure fields are preserved.
No consumer adaptation is included or required.

## Users

The table includes every module listed by `tools/downstream.py` with all 37 original public
names passed to `--uses`, including transitive importers and false positives from names such as
`Hom` and `identity`. Holders are the claim records at inspection time. All consumer signatures
retain their original mathematical meaning.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ClopenStrictSystemComparison` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoefficientSystemDerivedComparison` | V5 | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportCoefficientAction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportFiniteAction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportReductionTower` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportReductionTowerConstruction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | T5 | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralDirectImageTower` | M2 | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.MixedReductionUnit` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassChern` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TwConventions` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Unchanged signatures and definitions; available through the same public import. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Transitive importer or generic-name search hit; public re-export preserves its interface. |
| `Sheaf.Paper.CoefficientLevelOrdinaryImages` | unclaimed | Uses the moved coefficient quotient sheaf, level modules, and restriction interface. |
| `Sheaf.Paper.CoefficientSystemImageData` | unclaimed | Uses the moved coefficient quotient sheaf, quotient map, and level modules interface. |
| `Sheaf.Paper.CoefficientSystemOrdinaryImages` | unclaimed | Uses the moved coefficient restriction, coefficient system, and evaluation interface. |
| `Sheaf.Paper.CoefficientSystemUnboundedComparison` | unclaimed | Uses the moved level modules, coefficient system, and derived evaluation package interface. |
| `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint` | R6 | Item: definitions move verbatim to Models; final theorem signature stays identical. |
| `TargetsCheck` | unclaimed (aggregate) | All declarations and public imports remain available through the original module. |
| `WeilConjectures` | unclaimed (aggregate) | All declarations and public imports remain available through the original module. |

## Status

landed 20261020T235620-L-1196128 2026-10-20 (merge of deliver/R6/Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint)
