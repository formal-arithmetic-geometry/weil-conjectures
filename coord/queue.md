# Work queue

223 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (70 clusters, 2492 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Algebra.Homology.FilteredTensorGradedComparison` | 2208 | Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy, Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses, Sheaf.Algebra | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison` | 69 | Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition, Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibili | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.FilteredHomComplexInvariance` | 20 | Sheaf.Algebra.Homology.FiniteFilteredLocalization, Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso` | 20 | Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents, Sheaf.AlgebraicGeometry.QCohTensorResolutionCompariso | error: failed in the global build (no message located) |
| `Sheaf.Paper.EtaleCENormalizedRowPresentations` | 18 | Sheaf.Paper.EtaleCERowCyclesNaturality | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization` | 13 | Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso` | 11 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization` | 9 |  | error: failed in the global build (no message located) |
| `Sheaf.Paper.HypercoverInjectiveModuleRow` | 8 |  | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration` | 6 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux` | 6 |  | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology` | 5 | Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof` | 5 | Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 5 | Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback` | 4 | Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback, Sheaf.AlgebraicGeometry.CoherentPowerComparison | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts` | 4 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions` | 4 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact` | 3 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionAssociativity` | 3 | Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps` | 3 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange` | 3 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts` | 3 |  | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.SplitFlatFilteredSheafModels` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.TermwiseTorAcyclicBaseComparison` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.FormalGraphDiscrepancyZero` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.CategoryTheory.LerayFiveTerm` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` | 2 |  | error: failed in the global build (no message located) |
| `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.FieldFibreHomology` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.SchemeIsoPerfectLocalTransport` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.CategoryTheory.EdgeCollapse` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.RingTheory.ProjectiveDimensionSESKernel` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.Cohomology.Serre` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence` | 1 |  | error: failed in the global build (no message located) |

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
