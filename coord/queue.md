# Work queue

67 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (24 clusters, 2023 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.ConstructibleCoefficientHomologyTriangulated` | 1 |  | error: Sheaf/Paper/ConstructibleCoefficientHomologyTriangulated.lean:61:10: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | Sh |
| `Sheaf.Paper.FinitePerfectAdicRealization` | 1 |  | error: Sheaf/Paper/FinitePerfectAdicRealization.lean:83:45: error(lean.unknownIdentifier): Unknown identifier `FinitePerfectModelsCompatible` | | Note: It is no |
| `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules` | 1 |  | error: Sheaf/AlgebraicGeometry/CoefficientConstructibleEtaleModules.lean:111:10: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` |
| `Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension fail |
| `Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalUnderivedSectionsMate.lean:392:4: error: Application type mismatch: The argument | Functor.whiskerRight (baseChangeMap |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality f |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturali |
| `Sheaf.Paper.ModuleCupKInjectiveTarget` | 1 |  | error: Sheaf/Paper/ModuleCupKInjectiveTarget.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedTensorStructure failed, environment already contains 'Algebr |
| `Sheaf.CategoryTheory.GoodTruncationTotalDecalage` | 1 |  | error: Sheaf/CategoryTheory/GoodTruncationTotalDecalage.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'CategoryTh |
| `Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/AffinePerfectResidueModelNaturality.lean:84:19: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Modules |
| `Sheaf.Algebra.Homology.FilteredTensorGradedComparison` | 1 |  | error: Sheaf/Algebra/Homology/FilteredTensorGradedComparison.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'Categ |
| `Sheaf.Paper.EtaleCERowCyclesNaturality` | 1 |  | error: Sheaf/Paper/EtaleCERowCyclesNaturality.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'CategoryTheory.Decre |
| `Sheaf.RingTheory.AuslanderBuchsbaum` | 1 |  | error: Sheaf/RingTheory/AuslanderBuchsbaum.lean:52:8: error(lean.unknownIdentifier): Unknown identifier `depth_subsingleton` | Sheaf/RingTheory/AuslanderBuchsba |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalDerivedExchangeLeray.lean:6:0: error: import Sheaf.AlgebraicGeometry.StrictHenselization failed, environment already c |
| `Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration` | 1 |  | error: Sheaf/Algebra/Homology/FirstQuadrantVerticalConeFiltration.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains ' |
| `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute` | 1 |  | error: Sheaf/AlgebraicGeometry/RingedSpaceTensorPullbackAbsolute.lean:56:16: error(lean.unknownIdentifier): Unknown constant `SheafOfModules.changeOfRings` | |  |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean:26:23: error(lean.unknownIdentifier): Unknown identifier `Field` | | Note: A public declaration `Fi |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentFrobeniusPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality faile |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel` | 1 |  | error: Sheaf/AlgebraicGeometry/Morphisms/StrictHenselRootFiniteEtaleModel.lean:169:18: error(lean.unknownIdentifier): Unknown identifier `strictHenselization_st |
| `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` | 1 |  | error: Sheaf/CategoryTheory/FilteredHomotopySpectralSequence.lean:6:0: error: import WeilConjectures.CategoryTheory.CanonicalFiltration failed, environment alre |
| `Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof` | 1 |  | error: Sheaf/AlgebraicGeometry/AffinePerfectTensorRoof.lean:146:10: error(lean.unknownIdentifier): Unknown constant `CochainComplex.IsAcyclicTensorKFlat` | | No |
| `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas` | 1 |  | error: Sheaf/AlgebraicGeometry/RawModuleScalarPullbackFormulas.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors faile |
| `Sheaf.Paper.FlatFilteredComplexComparison` | 1 |  | error: Sheaf/Paper/FlatFilteredComplexComparison.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'CategoryTheory.De |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 32, stage 3 161 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (6)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.Sites.FpStalkRealization` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | - | 3 | proof | 3 |
| `Sheaf.Paper.SitePointReconstructionSets` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized` | - | 1 | proof | 21 |

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
