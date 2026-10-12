# Work queue

107 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (8)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-strict-local-exchange` | 1003 | sorry_here |
| `lemma-weil-pbc-curve-normalization-constant` | 1008 | sorry_here |
| `lemma-weil-pbc-smooth-curve-artin-schreier` | 1008 | sorry_here |
| `lemma-weil-pbc-smooth-curve-kummer-localization` | 1008 | sorry_here |
| `lemma-weil-pbc-curve-dense-open-reduction` | 1009 | sorry_here |
| `lemma-weil-pbc-normalization-exact-sequence` | 1009 | sorry_here |
| `lemma-weil-pbc-stein-connectedness` | 2006 | rests_on_sorry |
| `thm-weil-pbc-stein-inputs` | 2007 | sorry_here |

## Stage 2: nodes to state (1)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-nagata-finite-presentation-descent` | 3 | state | 3 |

Not open yet: 42 nodes that wait for stage 1, 3 nodes that wait for a statement dependency.

## Stage 3: modules to prove (98)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | 1 | 3 | proof |
| `Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit` | 2 | 2 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations` | 2 | 2 | proof |
| `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison` | 2 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | 2 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | 2 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Gabber` | 2 | 4 | proof |
| `Sheaf.AlgebraicGeometry.ConstantExtensionCover` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues` | 3 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericNeighbourhood` | 4 | 1 | proof |
| `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` | 4 | 1 | proof |
| `Sheaf.ConstructibleSheaf.LocallyConstantRetraction` | 4 | 1 | proof |
| `Sheaf.Paper.ZeroDimensionalEtaleCohomologyIso` | 4 | 1 | proof |
| `Sheaf.Paper.ZeroDimensionalGlobalSectionsExact` | 4 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleColimitCocone` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleFilteredData` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteSelection` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange` | 5 | 2 | proof |
| `Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk` | 5 | 1 | proof |
| `Sheaf.RingTheory.StrictlyHenselianOfDimensionZero` | 5 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` | 5 | 3 | proof |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | 5 | 4 | proof |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit` | 6 | 1 | proof |
| `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction` | 6 | 1 | proof |
| `Sheaf.CategoryTheory.SiteCechMathlibComparison` | 6 | 1 | proof |
| `Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic` | 6 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` | 6 | 6 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients` | 6 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` | 6 | 2 | proof |
| `Sheaf.AlgebraicGeometry.ConstantRingModuleSheafEquivalence` | 7 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion` | 7 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison` | 7 | 1 | proof |
| `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation` | 7 | 1 | proof |
| `Sheaf.Topology.ClosedUnionCohomologyVanishing` | 7 | 1 | proof |
| `Sheaf.Topology.CohomologyReductionConstantSubsheaves` | 7 | 1 | proof |
| `Sheaf.Topology.ConstantSubsheafFiniteFiltration` | 7 | 1 | proof |
| `Sheaf.Topology.NoetherianOpenClosedCohomologySequence` | 7 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival` | 7 | 3 | proof |
| `Sheaf.Topology.FlasqueZariskiAcyclic` | 8 | 1 | proof |
| `Sheaf.Topology.IrreducibleConstantSections` | 8 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | 8 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading` | 8 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Morphisms.Slicing` | 8 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | 8 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum` | 8 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition` | 8 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing` | 9 | 1 | proof |
| `Sheaf.Topology.Sheaves.LerayAcyclicComparison` | 9 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | 9 | 2 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf` | 9 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | 10 | 2 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality` | 10 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier` | 10 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Integral.BaseChange` | 10 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.Brauer` | 11 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.EffectiveDescent` | 11 | 4 | proof |
| `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality` | 11 | 1 | proof |
| `WeilConjectures.SixFunctors.Integral.Exact` | 11 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank` | 12 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity` | 12 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic` | 12 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` | 12 | 9 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field` | 12 | 2 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints` | 12 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv` | 12 | 2 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring` | 12 | 6 | proof |
| `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme` | 12 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Sites.BrauerGroup` | 12 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Serre` | 13 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.TangentSpace` | 13 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.TheoremOfCube` | 13 | 2 | proof |
| `WeilConjectures.RingTheory.HopfAlgebra.Cartier` | 14 | 1 | proof |

Waiting, not claimable: 2 modules whose proof uses a node that has no Lean declaration yet.

| module | distance to a target | sorry |
|---|---|---|
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | 3 | 4 |
| `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` | 10 | 2 |
