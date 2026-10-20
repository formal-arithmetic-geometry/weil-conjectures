# Work queue

108 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (44 clusters, 2382 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.IntegralConstructibleSerre` | 1 |  | error: Sheaf/Paper/IntegralConstructibleSerre.lean:43:4: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.ObjectProperty.IsClosedUnderKernels` |  |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageRawDiagram.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback failed |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean:1195:0: error: unexpected token 'by'; expected command | |
| `Sheaf.AlgebraicGeometry.ClosedSupportStratumHom` | 1 |  | error: Sheaf/AlgebraicGeometry/ClosedSupportStratumHom.lean:222:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class | (i)_*⟦Λ⟧.Prese |
| `Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension fail |
| `Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology` | 1 |  | error: Sheaf/AlgebraicGeometry/KFlatStalkResidueCohomology.lean:62:10: error(lean.unknownIdentifier): Unknown constant `CochainComplex.IsAcyclicTensorKFlat` | C |
| `Sheaf.CategoryTheory.BrownRepresentabilityConstruction` | 1 |  | error: Sheaf/CategoryTheory/BrownRepresentabilityConstruction.lean:49:50: error(lean.unknownIdentifier): Unknown identifier `IsCompactObject` | | Note: A public |
| `Sheaf.AlgebraicGeometry.RelativeMVResolvedOpenRoofComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/RelativeMVResolvedOpenRoofComparison.lean:69:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irr |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean:548:4: error: Type mismatch | isLeftDerivedFunctor₂_upperStar |
| `Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalLocalizedHomGerm.lean:57:6: error: Application type mismatch: The argument | ((Scheme.strictHenselizationStructuralMap |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality f |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturali |
| `Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme` | 1 |  | error: Sheaf/AlgebraicGeometry/ZeroSupportFiniteScheme.lean:70:26: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.RingedSpace.IsCoherent` |  |
| `Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarCupModuleCupCompatibility.lean:112:9: error(lean.unknownIdentifier): Unknown identifier `scalarCohomology` | | Note: A publ |
| `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso` | 1 |  | error: Sheaf/AlgebraicGeometry/StalkDerivedExtensionComparisonIso.lean:83:16: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environment do |
| `Sheaf.RingTheory.BoundedProjectiveResolutionDimension` | 1 |  | error: Sheaf/RingTheory/BoundedProjectiveResolutionDimension.lean:6:0: error: import WeilConjectures.RingTheory.GlobalDimension failed, environment already cont |
| `Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso` | 1 |  | error: Sheaf/AlgebraicGeometry/QCohTensorResolutionChartComparisonIso.lean:1:0: error: import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde failed, environment a |
| `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization` | 1 |  | error: Sheaf/AlgebraicGeometry/SchemeOrdinaryEvaluationLocalization.lean:40:27: error: failed to solve universe constraint | ?u.43 + 1 =?= u | while trying to u |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology` | 1 |  | error: Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAffineLocalCohomology.lean:79:11: error(lean.invalidField): Invalid field `Modules`: The environment do |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalDerivedExchangeLeray.lean:6:0: error: import Sheaf.AlgebraicGeometry.StrictHenselization failed, environment already c |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean:26:23: error(lean.unknownIdentifier): Unknown identifier `Field` | | Note: A public declaration `Fi |
| `Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant` | 1 |  | error: Sheaf/AlgebraicGeometry/SmoothDiagonalDualizingDeterminant.lean:6:0: error: import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex failed, environme |
| `Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization` | 1 |  | error: Sheaf/Algebra/Homology/AffineTildePushforwardHomologyFactorization.lean:30:25: error(lean.synthInstanceFailed): failed to synthesize instance of type cla |
| `Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization` | 1 |  | error: Sheaf/Algebra/Homology/PrescribedTensorCohomologyModelRealization.lean:5:0: error: import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyMod |
| `Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions` | 1 |  | error: Sheaf/AlgebraicGeometry/FormalSecondIdealAlgebraizationTransitions.lean:117:22: error: type expected, got | (IsNoetherian ↥X : (M : Type ?u.3) → [inst :  |
| `Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons` | 1 |  | error: Sheaf/AlgebraicGeometry/TensorModelRestrictionComparisons.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation failed, env |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarCohomologyPullbackSquare.lean:106:18: error(lean.unknownIdentifier): Unknown identifier `Field` | | Note: A public declarat |
| `Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` | 1 |  | error: Sheaf/Algebra/Homology/AffinePushforwardComparisonFactorization.lean:25:0: error: failed to solve universe constraint | u + 1 =?= u | while trying to uni |
| `Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineKoszulSectionRoof.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation failed, environment a |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryChainNaturality.lean:189:10: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environ |
| `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentFrobeniusPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality faile |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedDirectImageCompositionUnitLaws.lean:46:15: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A public d |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackCompositionCounitNormalization.lean:28:17: error: failed to set `[local irreducible]`, `derivedPullback` is curren |
| `Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange` | 1 |  | error: Sheaf/AlgebraicGeometry/EtaleGenericDirectImageExchange.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison fail |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageRawAffineImageRep.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback |
| `Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` | 1 |  | error: Sheaf/AlgebraicGeometry/OpenPinnedSourceCounitTriangle.lean:56:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irreducib |
| `Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` | 1 |  | error: Sheaf/RingTheory/ResidueFieldProjectiveDimensionDepth.lean:1:0: error: import WeilConjectures.RingTheory.GlobalDimension failed, environment already cont |
| `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor` | 1 |  | error: Sheaf/Algebra/Homology/TorIndependentProjectiveComplexTensor.lean:57:5: error(lean.unknownIdentifier): Unknown identifier `HasDerivedCategory` | | Note:  |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumCompositionUnitSquare.lean:189:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irr |
| `Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumUnitNormalization.lean:29:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irreduci |
| `Sheaf.AlgebraicGeometry.FieldFibreHomology` | 1 |  | error: Sheaf/AlgebraicGeometry/FieldFibreHomology.lean:41:6: error: Application type mismatch: The argument | (derivedPullback g).obj (DerivedCategory.Q.obj K)  |
| `Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore` | 1 |  | error: Sheaf/AlgebraicGeometry/PicardTermwiseCompositeCounitCore.lean:29:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irredu |
| `Sheaf.AlgebraicGeometry.SchemeIsoPerfectLocalTransport` | 1 |  | error: Sheaf/AlgebraicGeometry/SchemeIsoPerfectLocalTransport.lean:171:2: error: failed to solve universe constraint | ?u.539 + 1 =?= u | while trying to unify  |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 1, stage 2 32, stage 3 137 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (4)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 8 | 1 | disputed | route |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | - | 3 | proof | 3 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |

## Stage 3: held for an open upstream PR (19)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
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
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
