# Work queue

212 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (51 clusters, 2492 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses` | 2208 | Sheaf.AlgebraicGeometry.AffinePushforwardColimit, Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare, Sheaf.AlgebraicGeo | error: Sheaf/Algebra/Homology/RhomGlobalSectionsOfUniverses.lean:6:0: error: import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology failed, environment a |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison` | 69 | Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition, Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibili | error: Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAffineCechComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomol |
| `Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents` | 20 | Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso, Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNa | error: Sheaf/AlgebraicGeometry/QCohTensorResolutionChartTensorComponents.lean:1:0: error: import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSingleTen |
| `Sheaf.Paper.EtaleCENormalizedRowPresentations` | 18 | Sheaf.Paper.EtaleCERowCyclesNaturality | error: Sheaf/Paper/EtaleCENormalizedRowPresentations.lean:319:42: error: overloaded, errors | Unknown constant `Functor.kInjective_computes` | | Unknown constan |
| `Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization` | 13 | Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers | error: Sheaf/Algebra/Homology/AffineTildePushforwardHomologyFactorization.lean:30:25: error(lean.synthInstanceFailed): failed to synthesize instance of type cla |
| `Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso` | 11 |  | error: Sheaf/AlgebraicGeometry/SelfTorConormalDualChartIso.lean:109:82: error: Application type mismatch: The argument | φ | has type | (U : ↑Y.affineOpens) → |
| `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization` | 9 |  | error: Sheaf/AlgebraicGeometry/SchemeOrdinaryEvaluationLocalization.lean:40:27: error: failed to solve universe constraint | ?u.43 + 1 =?= u | while trying to u |
| `Sheaf.Paper.HypercoverInjectiveModuleRow` | 8 |  | error: Sheaf/Paper/HypercoverInjectiveModuleRow.lean:114:11: error(lean.synthInstanceFailed): failed to synthesize instance of type class | CommRing R | | Hint: |
| `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology` | 5 | Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization | error: Sheaf/Algebra/Homology/DerivedTensorLocalizationCohomology.lean:5:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel fail |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 5 | Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback` | 4 | Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback, Sheaf.AlgebraicGeometry.CoherentPowerComparison | error: Sheaf/AlgebraicGeometry/CoherentEtaleComparisonPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality |
| `Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions` | 4 |  | error: Sheaf/AlgebraicGeometry/FormalSecondIdealAlgebraizationTransitions.lean:117:22: error: type expected, got | (IsNoetherian ↥X : (M : Type ?u.3) → [inst :  |
| `Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact` | 3 |  | error: Sheaf/AlgebraicGeometry/AffineOpenLocalizedTensorExact.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes failed,  |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionAssociativity` | 3 | Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws | error: Sheaf/AlgebraicGeometry/DerivedDirectImageCompositionAssociativity.lean:44:15: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A pub |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts` | 3 |  | error: Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/FiniteHypercoverDescentParts.lean:1175:0: error: Unexpected name `AlgebraicGeometry` after `end`: T |
| `Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` | 2 |  | error: Sheaf/Algebra/Homology/AffinePushforwardComparisonFactorization.lean:25:0: error: failed to solve universe constraint | u + 1 =?= u | while trying to uni |
| `Sheaf.Algebra.Homology.TermwiseTorAcyclicBaseComparison` | 2 |  | error: Sheaf/Algebra/Homology/TermwiseTorAcyclicBaseComparison.lean:6:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel failed, |
| `Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels` | 2 |  | error: Sheaf/AlgebraicGeometry/AffineCoordinateModuleModels.lean:89:4: error(lean.unknownIdentifier): Unknown constant `CochainComplex.IsAcyclicTensorKFlat` | | |
| `Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData` | 2 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumStalkCoordinateData.lean:2:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel faile |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality` | 2 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryChainNaturality.lean:189:10: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environ |
| `Sheaf.AlgebraicGeometry.FormalGraphDiscrepancyZero` | 2 |  | error: Sheaf/AlgebraicGeometry/FormalGraphDiscrepancyZero.lean:60:9: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A public declaration ` |
| `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists` | 2 |  | error: Sheaf/AlgebraicGeometry/GrothendieckExistenceEasyFromExists.lean:71:51: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A public dec |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 2 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageRawAffineImageRep.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback |
| `Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` | 2 |  | error: Sheaf/AlgebraicGeometry/OpenPinnedSourceCounitTriangle.lean:56:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irreducib |
| `Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree` | 2 |  | error: Sheaf/AlgebraicGeometry/RegularCurveTorsionfreeFree.lean:60:17: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.RingedSpace.IsCoherent |
| `Sheaf.CategoryTheory.LerayFiveTerm` | 2 |  | error: Sheaf/CategoryTheory/LerayFiveTerm.lean:40:25: error(lean.unknownIdentifier): Unknown identifier `BigradedExactCouple` | | Note: A public declaration `Bi |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` | 2 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/MorphismDefs.lean:119:0: error: Unexpected name `BaseChangeTransformation` after |
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

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 2, stage 2 32, stage 3 156 items.

## Stage 1: nodes to split (1)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-pushforward-comp-monoidal` | - | sorry_here |

## Stage 2: nodes to state (0)


Not open yet: 300 nodes that below a finished node, not needed, 85 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (30)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | 6 | 1 | proof | route |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | 9 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 14 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 16 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifUpperShriek` | 16 | 1 | proof | route |
| `WeilConjectures.ConstructibleSheaf.Noetherian` | 19 | 2 | proof | route |
| `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` | - | 7 | proof | 2 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SignedDoubleHomCone` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SignedFibreTriangulated` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.DncAffineBlowupComplement` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.StandardGroupSchemes` | - | 12 | proof | 4 |
| `Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge` | - | 1 | proof | 4 |
| `Sheaf.FieldTheory.BertiniFieldExtension` | - | 1 | proof | 4 |
| `Sheaf.Paper.InvertibleTensorScalarExtension` | - | 1 | proof | 4 |
| `Sheaf.Paper.KFlatConeComparison` | - | 1 | proof | 4 |
| `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` | - | 4 | proof | 4 |
| `Sheaf.SixFunctors.CompactificationOverBase` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatFinitePresentationRetract` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat` | - | 1 | proof | 5 |
| `Sheaf.Paper.RingComplexGodementFunctorial` | - | 1 | proof | 5 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement` | - | 1 | proof | 7 |
| `Sheaf.CategoryTheory.DualizableJointlyConservativeLocality` | - | 1 | proof | 7 |
| `Sheaf.Paper.EtaleLisseFiltrationDevissage` | - | 1 | proof | 10 |
| `Sheaf.RingTheory.ColimOfLocalizations` | - | 1 | proof | 13 |
| `Sheaf.Algebra.Homology.IntegerFlatRepresentative` | - | 1 | proof | 17 |

## Stage 3: held for an open upstream PR (20)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
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
| `WeilConjectures.WeilSheaf.Finiteness` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
