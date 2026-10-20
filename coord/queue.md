# Work queue

184 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (96 clusters, 2492 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.FiniteOrderedCechCoefficientMap` | 1 |  | error: Sheaf/Paper/FiniteOrderedCechCoefficientMap.lean:145:24: error(lean.unknownIdentifier): Unknown identifier `alternatingCechZero_naturality` | Sheaf/Paper |
| `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses` | 1 |  | error: Sheaf/Algebra/Homology/RhomGlobalSectionsOfUniverses.lean:6:0: error: import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology failed, environment a |
| `Sheaf.Paper.IntegralConstructibleKernels` | 1 |  | error: Sheaf/Paper/IntegralConstructibleKernels.lean:721:4: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.ObjectProperty.IsClosedUnderKernels` |
| `Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle` | 1 |  | error: Sheaf/AlgebraicGeometry/LocallyFreeTensorSingle.lean:58:10: error(lean.unknownIdentifier): Unknown identifier `locallyFinitelyPresented_of_isZero` | Shea |
| `Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage` | 1 |  | error: Sheaf/AlgebraicGeometry/BoundedConstructibleDevissage.lean:38:12: error(lean.unknownIdentifier): Unknown identifier `constructible_of_iso` | Sheaf/Algebr |
| `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/UnboundedAbelianExchangeComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison f |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageRawDiagram.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback failed |
| `Sheaf.Paper.CondensedInternalHomSections` | 1 |  | error: Sheaf/Paper/CondensedInternalHomSections.lean:76:5: error: overloaded, errors | Unknown constant `Mod.relativeTensorRightIso` | | Unknown constant `Categ |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean:1195:0: error: unexpected token 'by'; expected command | |
| `Sheaf.AlgebraicGeometry.ProEtalePullbackInternalHom` | 1 |  | error: Sheaf/AlgebraicGeometry/ProEtalePullbackInternalHom.lean:46:7: error: overloaded, errors | Unknown constant `Mod.relativeTensorRightIso` | | Unknown cons |
| `Sheaf.Paper.LisseFiniteHomLift` | 1 |  | error: Sheaf/Paper/LisseFiniteHomLift.lean:73:5: error: overloaded, errors | Unknown constant `Mod.relativeTensorRightIso` | | Unknown constant `CategoryTheory. |
| `Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension fail |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:97:0: error: Unexpected name `CoefficientMap` after `end` |
| `Sheaf.Paper.ContinuousAlgClConstructibleTor` | 1 |  | error: Sheaf/Paper/ContinuousAlgClConstructibleTor.lean:109:29: error: overloaded, errors | Unknown constant `Mod.relativeTensorRightIso` | | Unknown constant ` |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | 1 |  | error: Sheaf/AlgebraicGeometry/VectorBundleZeroSection.lean:55:3: error(lean.unknownIdentifier): Unknown identifier `affine_morphism_relative_spec` | | Note: A  |
| `Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology` | 1 |  | error: Sheaf/AlgebraicGeometry/KFlatStalkResidueCohomology.lean:62:10: error(lean.unknownIdentifier): Unknown constant `CochainComplex.IsAcyclicTensorKFlat` | C |
| `Sheaf.AlgebraicGeometry.RelativeMVDirectImageSquareLocalization` | 1 |  | error: Sheaf/AlgebraicGeometry/RelativeMVDirectImageSquareLocalization.lean:37:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[ |
| `Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/KFlatPullbackAdjunctionComparison.lean:29:10: error(lean.unknownIdentifier): Unknown constant `CochainComplex.IsAcyclicTensorKFla |
| `Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization` | 1 |  | error: Sheaf/SixFunctors/ProEtale/BaseChange/ComparisonSquareEtalePathNormalization.lean:239:6: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeomet |
| `Sheaf.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CounitStalkConditionFromLocalizedComparison.lean:5:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyM |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean:548:4: error: Type mismatch | isLeftDerivedFunctor₂_upperStar |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalMate` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedBaseChangeHorizontalMate.lean:177:0: error: failed to solve universe constraint | u + 1 =?= u | while trying to unify | Ca |
| `Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit` | 1 |  | error: Sheaf/AlgebraicGeometry/OpenFlatComplexStalkCounit.lean:5:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel failed, envi |
| `Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction` | 1 |  | error: Sheaf/AlgebraicGeometry/SourceCocycleExactRestriction.lean:92:7: error(lean.synthInstanceFailed): failed to synthesize instance of type class | G.Preserv |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality f |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturali |
| `Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor` | 1 |  | error: Sheaf/AlgebraicGeometry/FiniteSchemeCohomologyTensor.lean:74:10: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.RingedSpace.IsCoheren |
| `Sheaf.CategoryTheory.FilteredHomologyCoupleNormalization` | 1 |  | error: Sheaf/CategoryTheory/FilteredHomologyCoupleNormalization.lean:50:42: error(lean.invalidField): Invalid field `initialG`: The environment does not contain |
| `Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore` | 1 |  | error: Sheaf/RingTheory/StrictHenselizationSurjectiveQuotientCore.lean:43:23: error(lean.unknownIdentifier): Unknown identifier `quotientBaseChange_obj_iso` | S |
| `Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarCupResolutionClassCompatibility.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperat |
| `Sheaf.AlgebraicGeometry.AffinePushforwardColimit` | 1 |  | error: Sheaf/AlgebraicGeometry/AffinePushforwardColimit.lean:70:45: error(lean.invalidField): Invalid field `CommAlgebraSheaf`: The environment does not contain |
| `Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectCounit` | 1 |  | error: Sheaf/AlgebraicGeometry/LocalizedPullbackPerfectCounit.lean:107:23: error: failed to synthesize | B.PreservesZeroMorphisms | (deterministic) timeout at ` |
| `Sheaf.Paper.EtaleCENormalizedRowPresentations` | 1 |  | error: Sheaf/Paper/EtaleCENormalizedRowPresentations.lean:319:42: error: overloaded, errors | Unknown constant `Functor.kInjective_computes` | | Unknown constan |
| `Sheaf.Paper.ModuleCupResolutionFMap` | 1 |  | error: Sheaf/Paper/ModuleCupResolutionFMap.lean:205:19: error(lean.unknownIdentifier): Unknown identifier `moduleCohomologyFMap` | | Note: A public declaration  |
| `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso` | 1 |  | error: Sheaf/AlgebraicGeometry/StalkDerivedExtensionComparisonIsIso.lean:65:17: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environment  |
| `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore` | 1 |  | error: Sheaf/AlgebraicGeometry/StalkDerivedExtensionComparisonIsoCore.lean:115:16: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environme |
| `Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso` | 1 |  | error: Sheaf/AlgebraicGeometry/SelfTorConormalDualChartIso.lean:109:82: error: Application type mismatch: The argument | φ | has type | (U : ↑Y.affineOpens) → |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAffineCechComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomol |
| `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization` | 1 |  | error: Sheaf/AlgebraicGeometry/SchemeOrdinaryEvaluationLocalization.lean:40:27: error: failed to solve universe constraint | ?u.43 + 1 =?= u | while trying to u |
| `Sheaf.Paper.HypercoverInjectiveModuleRow` | 1 |  | error: Sheaf/Paper/HypercoverInjectiveModuleRow.lean:114:11: error(lean.synthInstanceFailed): failed to synthesize instance of type class | CommRing R | | Hint: |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations failed,  |
| `Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization` | 1 |  | error: Sheaf/Algebra/Homology/AffineTildePushforwardHomologyFactorization.lean:30:25: error(lean.synthInstanceFailed): failed to synthesize instance of type cla |
| `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology` | 1 |  | error: Sheaf/Algebra/Homology/DerivedTensorLocalizationCohomology.lean:5:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel fail |
| `Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization` | 1 |  | error: Sheaf/Algebra/Homology/PrescribedTensorCohomologyModelRealization.lean:5:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyMod |
| `Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions` | 1 |  | error: Sheaf/AlgebraicGeometry/FormalSecondIdealAlgebraizationTransitions.lean:117:22: error: type expected, got | (IsNoetherian ↥X : (M : Type ?u.3) → [inst :  |
| `Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents` | 1 |  | error: Sheaf/AlgebraicGeometry/QCohTensorResolutionChartTensorComponents.lean:1:0: error: import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSingleTen |
| `Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarCohomologyPullbackComposition.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperatio |
| `Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineOpenLocalizedTensorExact.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes failed,  |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumCounitSquare.lean:62:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environment does not c |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryRepresentativeCoherence.lean:113:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The |
| `Sheaf.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedDirectImagePastedCounitNormalization.lean:24:17: error: failed to set `[local irreducible]`, `derivedPullback` is currentl |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackCompositionLocalizedCounit.lean:26:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently  |
| `Sheaf.PoincareDuality.ConstructibleShiftSingle` | 1 |  | error: Sheaf/PoincareDuality/ConstructibleShiftSingle.lean:55:12: error(lean.unknownIdentifier): Unknown identifier `constructible_of_iso` | Sheaf/PoincareDuali |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/FiniteHypercoverDescentParts.lean:1175:0: error: Unexpected name `AlgebraicGeometry` after `end`: T |
| `Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` | 1 |  | error: Sheaf/Algebra/Homology/AffinePushforwardComparisonFactorization.lean:25:0: error: failed to solve universe constraint | u + 1 =?= u | while trying to uni |
| `Sheaf.Algebra.Homology.TermwiseTorAcyclicBaseComparison` | 1 |  | error: Sheaf/Algebra/Homology/TermwiseTorAcyclicBaseComparison.lean:6:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel failed, |
| `Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineCoordinateModuleModels.lean:89:4: error(lean.unknownIdentifier): Unknown constant `CochainComplex.IsAcyclicTensorKFlat` | | |
| `Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumStalkCoordinateData.lean:2:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel faile |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryChainNaturality.lean:189:10: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environ |
| `Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentEtaleComparisonPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality |
| `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentFrobeniusPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality faile |
| `Sheaf.AlgebraicGeometry.CoherentPowerComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentPowerComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality failed, |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionAssociativity` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedDirectImageCompositionAssociativity.lean:44:15: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A pub |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedDirectImageCompositionUnitLaws.lean:46:15: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A public d |
| `Sheaf.AlgebraicGeometry.FormalGraphDiscrepancyZero` | 1 |  | error: Sheaf/AlgebraicGeometry/FormalGraphDiscrepancyZero.lean:60:9: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A public declaration ` |
| `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists` | 1 |  | error: Sheaf/AlgebraicGeometry/GrothendieckExistenceEasyFromExists.lean:71:51: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A public dec |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageRawAffineImageRep.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback |
| `Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` | 1 |  | error: Sheaf/AlgebraicGeometry/OpenPinnedSourceCounitTriangle.lean:56:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irreducib |
| `Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree` | 1 |  | error: Sheaf/AlgebraicGeometry/RegularCurveTorsionfreeFree.lean:60:17: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.RingedSpace.IsCoherent |
| `Sheaf.CategoryTheory.LerayFiveTerm` | 1 |  | error: Sheaf/CategoryTheory/LerayFiveTerm.lean:40:25: error(lean.unknownIdentifier): Unknown identifier `BigradedExactCouple` | | Note: A public declaration `Bi |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/MorphismDefs.lean:119:0: error: Unexpected name `BaseChangeTransformation` after |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumCompositionUnitSquare.lean:189:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irr |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumCounitCompatibility.lean:28:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irredu |
| `Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumUnitNormalization.lean:29:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irreduci |
| `Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedSquareIsoPasting.lean:167:8: error: (kernel) deterministic timeout | Compiled in 45.6 s |
| `Sheaf.AlgebraicGeometry.FieldFibreHomology` | 1 |  | error: Sheaf/AlgebraicGeometry/FieldFibreHomology.lean:41:6: error: Application type mismatch: The argument | (derivedPullback g).obj (DerivedCategory.Q.obj K)  |
| `Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation` | 1 |  | error: Sheaf/AlgebraicGeometry/IsomorphicSingleTensorCounitEquation.lean:18:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irr |
| `Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux` | 1 |  | error: Sheaf/AlgebraicGeometry/OpenRestrictedCounitFactorizationAux.lean:12:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irr |
| `Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore` | 1 |  | error: Sheaf/AlgebraicGeometry/PicardTermwiseCompositeCounitCore.lean:29:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irredu |
| `Sheaf.AlgebraicGeometry.SchemeIsoPerfectLocalTransport` | 1 |  | error: Sheaf/AlgebraicGeometry/SchemeIsoPerfectLocalTransport.lean:171:2: error: failed to solve universe constraint | ?u.539 + 1 =?= u | while trying to unify  |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation` | 1 |  | error: Sheaf/AlgebraicGeometry/SingleComplexOpenBaseChangeCalculation.lean:22:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[i |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation` | 1 |  | error: Sheaf/AlgebraicGeometry/SingleComplexOpenRestrictedCounitCancellation.lean:24:17: error: failed to set `[local irreducible]`, `derivedPullback` is curren |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization` | 1 |  | error: Sheaf/AlgebraicGeometry/SingleComplexOpenUnitSquareFactorization.lean:40:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently ` |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/TorIndependentPerfectPullbackComparison.lean:6:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel |
| `Sheaf.CategoryTheory.EdgeCollapse` | 1 |  | error: Sheaf/CategoryTheory/EdgeCollapse.lean:44:11: error(lean.invalidField): Invalid field `LimitSubobjects`: The environment does not contain `CategoryTheory |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.Cohomology.Serre` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/Cohomology/Serre.lean:146:0: error: Unexpected name `AlgebraicGeometry` after `end`: The current se |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/EtaleFiniteDataDescent.lean:52:0: error: Unexpected name `AlgebraicGeometry` after `end`: The curre |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Charts.lean:67:12: error: redundant binder annotation update | Sheaf/UpstreamExtra/ |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Line.lean:66:10: error(lean.unknownIdentifier): Unknown identifier `subsingleton_ne |
| `Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/DeligneLaumon/Reduction/QuasiFiniteVanishing.lean:148:0: error: Unexpected name `LowerShriek` after `end`: The curren |
| `Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/FromJoel/Algebra/Homology/Embedding/CochainComplex.lean:38:0: error: Unexpected name `CochainComplex` after `end`: Th |
| `Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/FromJoel/Algebra/Homology/Embedding/CochainComplexTrunc.lean:41:12: error: redundant binder annotation update | Sheaf |
| `Sheaf.UpstreamExtra.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Proetale.lean:107:0: error: Unexpected name `OverMap` after `end`: The current sectio |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/Etale/Derived/UpperShriek.lean:104:0: error: Unexpected name `Unbounded` after `end`: The current section |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Coherence.lean:116:0: error: Unexpected name `Eta` after `end`: |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 2, stage 2 33, stage 3 134 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 301 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (10)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 7 | 1 | disputed | route |
| `Sheaf.Paper.LisseAdicSheaves` | 6 | 2 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 8 | 1 | proof | route |
| `Sheaf.CategoryTheory.BraidedSheafTensorGenerators` | 9 | 2 | proof | route |
| `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` | - | 2 | proof | 2 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact` | - | 1 | proof | 3 |
| `Sheaf.Paper.InvertibleTensorScalarExtension` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat` | - | 1 | proof | 5 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |

## Stage 3: held for an open upstream PR (22)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-six-functors-c1,bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | bundle/sec-smooth-purity-d2,prove2/sk-prop-sf-kunneth-ordinary |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.WeilSheaf.Finiteness` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
