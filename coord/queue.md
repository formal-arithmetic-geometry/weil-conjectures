# Work queue

79 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (28 clusters, 2128 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.CategoryTheory.RingedCechKoszulDualLimit` | 1 |  | error: Sheaf/CategoryTheory/RingedCechKoszulDualLimit.lean:452:11: error(lean.unknownIdentifier): Unknown constant `CochainComplex.telescopeShiftColimit` | Shea |
| `Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation` | 1 |  | error: Sheaf/AlgebraicGeometry/BoundedConstructibleTensorPreservation.lean:84:10: error(lean.unknownIdentifier): Unknown identifier `constructible_of_iso` | She |
| `Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension fail |
| `Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalLocalizedHomGerm.lean:57:6: error: Application type mismatch: The argument | ((Scheme.strictHenselizationStructuralMap |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality f |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturali |
| `Sheaf.Paper.GlobalTensorPullbackDerivedData` | 1 |  | error: Sheaf/Paper/GlobalTensorPullbackDerivedData.lean:100:9: error(lean.unknownIdentifier): Unknown constant `CochainComplex.tensorPullbackRingMap` | | Note:  |
| `Sheaf.Paper.GlobalTensorPullbackUnderivedData` | 1 |  | error: Sheaf/Paper/GlobalTensorPullbackUnderivedData.lean:6:0: error: import WeilConjectures.Algebra.Homology.KFlatPullback failed, environment already contains |
| `Sheaf.RingTheory.AuslanderBuchsbaum` | 1 |  | error: Sheaf/RingTheory/AuslanderBuchsbaum.lean:52:8: error(lean.unknownIdentifier): Unknown identifier `depth_subsingleton` | Sheaf/RingTheory/AuslanderBuchsba |
| `Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso` | 1 |  | error: Sheaf/AlgebraicGeometry/QCohTensorResolutionChartComparisonIso.lean:1:0: error: import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde failed, environment a |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalDerivedExchangeLeray.lean:6:0: error: import Sheaf.AlgebraicGeometry.StrictHenselization failed, environment already c |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic` | 1 |  | error: Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAcyclic.lean:62:15: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.RingedSpace.modu |
| `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux` | 1 |  | error: Sheaf/AlgebraicGeometry/RingedSpaceTensorPullbackAbsoluteAux.lean:1:0: error: import WeilConjectures.Algebra.Homology.KFlatPullback failed, environment a |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection` | 1 |  | error: Sheaf/AlgebraicGeometry/KoszulSelfExtConormalComparisonSurjection.lean:66:23: error(lean.unknownIdentifier): Unknown constant `SheafOfModules.existsUniqu |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite` | 1 |  | error: Sheaf/AlgebraicGeometry/Morphisms/StrictHenselRootNormalizationFinite.lean:190:28: error(lean.unknownIdentifier): Unknown identifier `strictHenselization |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale` | 1 |  | error: Sheaf/AlgebraicGeometry/Morphisms/StrictHenselRootNormalizationGenericEtale.lean:136:4: error(lean.unknownIdentifier): Unknown identifier `strictHenseliz |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean:26:23: error(lean.unknownIdentifier): Unknown identifier `Field` | | Note: A public declaration `Fi |
| `Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant` | 1 |  | error: Sheaf/AlgebraicGeometry/SmoothDiagonalDualizingDeterminant.lean:6:0: error: import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex failed, environme |
| `Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates` | 1 |  | error: Sheaf/Algebra/Homology/AffineTildeCoefficientPushforwardHomologyCoordinates.lean:31:25: error(lean.synthInstanceFailed): failed to synthesize instance of |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryDescentRepresentative.lean:51:10: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentFrobeniusPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality faile |
| `Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange` | 1 |  | error: Sheaf/AlgebraicGeometry/EtaleGenericDirectImageExchange.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison fail |
| `Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula` | 1 |  | error: Sheaf/AlgebraicGeometry/RawModuleScalarHomCompositeFormula.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors fa |
| `Sheaf.AlgebraicGeometry.TensorRoofTransposition` | 1 |  | error: Sheaf/AlgebraicGeometry/TensorRoofTransposition.lean:106:9: error(lean.unknownIdentifier): Unknown identifier `Scheme` | | Note: A public declaration `Sc |
| `Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity` | 1 |  | error: Sheaf/Algebra/Homology/AffinePushforwardCohomologyEdgeIdentity.lean:5:0: error: import Sheaf.AlgebraicGeometry.AffineDerivedCohomologyPresentation failed |
| `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas` | 1 |  | error: Sheaf/AlgebraicGeometry/RawModuleScalarPullbackFormulas.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors faile |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean:1:0: error: import Sheaf.SixFunctors.ProEtale.BaseChange.Smooth |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 32, stage 3 152 items.

## Stage 1: nodes to split (1)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `new-proetale-derived-module-pullback-monoidal` | - | none |

## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (2)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | - | 3 | proof | 3 |
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
