# Work queue

102 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (46 clusters, 2349 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated` | 1 |  | error: Sheaf/AlgebraicGeometry/EllAdicBoundedTriangulated.lean:84:33: error: Application type mismatch: The argument | R | has type | Sheaf (Scheme.ProEt.topolo |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageRawDiagram.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback failed |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | 1 |  | error: Sheaf/Paper/CondensedFlatCoefficientCalculus.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/local/build/RW/Sheaf/UpstreamExtra/WeilCon |
| `Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension fail |
| `Sheaf.Paper.IntegralConstantModelHeartClosure` | 1 |  | error: Sheaf/Paper/IntegralConstantModelHeartClosure.lean:290:2: error: Tactic `generalize` failed: result is not type correct | @CategoryTheory.ObjectProperty. |
| `Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/StalkFreeResidueCohomologyComparison.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/local/build/RW/Sheaf/Algeb |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean:548:4: error: Type mismatch | isLeftDerivedFunctor₂_upperStar |
| `Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalLocalizedHomGerm.lean:57:6: error: Application type mismatch: The argument | ((Scheme.strictHenselizationStructuralMap |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality f |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturali |
| `Sheaf.Paper.GlobalTensorPullbackKFlat` | 1 |  | error: Sheaf/Paper/GlobalTensorPullbackKFlat.lean:6:0: error: import WeilConjectures.Algebra.Homology.KFlatPullback failed, environment already contains 'Cochai |
| `Sheaf.Paper.GlobalTensorPullbackUnderivedData` | 1 |  | error: Sheaf/Paper/GlobalTensorPullbackUnderivedData.lean:6:0: error: import WeilConjectures.Algebra.Homology.KFlatPullback failed, environment already contains |
| `Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport` | 1 |  | error: Sheaf/AlgebraicGeometry/EulerCharZeroDimSupport.lean:55:10: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.RingedSpace.IsCoherent` |  |
| `Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedFiberCohomologyBaseChange.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/local/build/RW/Sheaf/Algebraic |
| `Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing` | 1 |  | error: Sheaf/AlgebraicGeometry/ResidueBettiZeroOfTensorVanishing.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/local/build/RW/Sheaf/Algebrai |
| `Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExternalCupModuleComparison.lean:55:11: error(lean.synthInstanceFailed): failed to synthesize instance of type class | NonA |
| `Sheaf.RingTheory.AuslanderBuchsbaum` | 1 |  | error: Sheaf/RingTheory/AuslanderBuchsbaum.lean:52:8: error(lean.unknownIdentifier): Unknown identifier `depth_subsingleton` | Sheaf/RingTheory/AuslanderBuchsba |
| `Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso` | 1 |  | error: Sheaf/AlgebraicGeometry/QCohTensorResolutionChartComparisonIso.lean:1:0: error: import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde failed, environment a |
| `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization` | 1 |  | error: Sheaf/AlgebraicGeometry/SchemeOrdinaryEvaluationLocalization.lean:40:27: error: failed to solve universe constraint | ?u.43 + 1 =?= u | while trying to u |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages` | 1 |  | error: Sheaf/AlgebraicGeometry/PicardExternalCoefficientsDirectImages.lean:120:11: error(lean.unknownIdentifier): Unknown identifier `externalCupCoefficients` | |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalDerivedExchangeLeray.lean:6:0: error: import Sheaf.AlgebraicGeometry.StrictHenselization failed, environment already c |
| `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux` | 1 |  | error: Sheaf/AlgebraicGeometry/RingedSpaceTensorPullbackAbsoluteAux.lean:1:0: error: import WeilConjectures.Algebra.Homology.KFlatPullback failed, environment a |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean:26:23: error(lean.unknownIdentifier): Unknown identifier `Field` | | Note: A public declaration `Fi |
| `Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant` | 1 |  | error: Sheaf/AlgebraicGeometry/SmoothDiagonalDualizingDeterminant.lean:6:0: error: import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex failed, environme |
| `Sheaf.Paper.IntegralReductionConstructible` | 1 |  | error: Sheaf/Paper/IntegralReductionConstructible.lean:164:2: error: Tactic `generalize` failed: result is not type correct | @CategoryTheory.ObjectProperty.IsC |
| `Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization` | 1 |  | error: Sheaf/Algebra/Homology/AffineTildePushforwardHomologyFactorization.lean:30:25: error(lean.synthInstanceFailed): failed to synthesize instance of type cla |
| `Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare` | 1 |  | error: Sheaf/Algebra/Homology/AffineTensorCohomologyLocalizationSquare.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/local/build/RW/Sheaf/Al |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction` | 1 |  | error: Sheaf/AlgebraicGeometry/TensorModelRestrictionAdjunction.lean:6:0: error: import Sheaf.Algebra.Homology.DerivedInternalHom failed, environment already co |
| `Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineKoszulSectionRoof.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation failed, environment a |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryChainNaturality.lean:189:10: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The environ |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryDescentRepresentative.lean:51:10: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentFrobeniusPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality faile |
| `Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange` | 1 |  | error: Sheaf/AlgebraicGeometry/EtaleGenericDirectImageExchange.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison fail |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageRawAffineImageRep.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback |
| `Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` | 1 |  | error: Sheaf/AlgebraicGeometry/OpenPinnedSourceCounitTriangle.lean:56:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irreducib |
| `Sheaf.Paper.IntegralReductionConservative` | 1 |  | error: Sheaf/Paper/IntegralReductionConservative.lean:55:2: error: Tactic `generalize` failed: result is not type correct | @CategoryTheory.ObjectProperty.IsClo |
| `Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` | 1 |  | error: Sheaf/RingTheory/ResidueFieldProjectiveDimensionDepth.lean:1:0: error: import WeilConjectures.RingTheory.GlobalDimension failed, environment already cont |
| `Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity` | 1 |  | error: Sheaf/Algebra/Homology/AffinePushforwardCohomologyEdgeIdentity.lean:5:0: error: import Sheaf.AlgebraicGeometry.AffineDerivedCohomologyPresentation failed |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumCompositionUnitSquare.lean:189:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irr |
| `Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineSpectrumUnitNormalization.lean:29:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irreduci |
| `Sheaf.AlgebraicGeometry.FieldFibreHomology` | 1 |  | error: Sheaf/AlgebraicGeometry/FieldFibreHomology.lean:41:6: error: Application type mismatch: The argument | (derivedPullback g).obj (DerivedCategory.Q.obj K)  |
| `Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore` | 1 |  | error: Sheaf/AlgebraicGeometry/PicardTermwiseCompositeCounitCore.lean:29:17: error: failed to set `[local irreducible]`, `derivedPullback` is currently `[irredu |
| `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition` | 1 |  | error: Sheaf/AlgebraicGeometry/ProperDerivedDirectImageComposition.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/local/build/RW/Sheaf/Algebr |
| `Sheaf.AlgebraicGeometry.SchemeIsoPerfectLocalTransport` | 1 |  | error: Sheaf/AlgebraicGeometry/SchemeIsoPerfectLocalTransport.lean:171:2: error: failed to solve universe constraint | ?u.539 + 1 =?= u | while trying to unify  |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean:1:0: error: import Sheaf.SixFunctors.ProEtale.BaseChange.Smooth |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 1, stage 2 32, stage 3 143 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (3)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
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
