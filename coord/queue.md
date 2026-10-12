# Work queue

62 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (5)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-strict-local-exchange` | 1003 | sorry_here |
| `lemma-weil-pbc-smooth-curve-artin-schreier` | 1007 | sorry_here |
| `lemma-weil-pbc-smooth-curve-kummer-localization` | 1007 | sorry_here |
| `lemma-weil-pbc-stein-connectedness` | 2006 | rests_on_sorry |
| `thm-weil-pbc-stein-inputs` | 2007 | sorry_here |

## Stage 2: nodes to state (4)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-nagata-relative-gluing-valid-stage` | 2 | state | 5 |
| `lem-sc-boundary-cech-injective-middle` | 1 | state | 1 |
| `lem-sc-hilb-dominating-power` | 1 | state | 0 |
| `lem-sc-qcoh-complex-alternating-cech-derived-sections` | 1 | state | 0 |

Not open yet: 42 nodes that wait for stage 1, 5 nodes that wait for a statement dependency.

## Stage 3: modules to prove (53)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | 1 | 6 | proof |
| `Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit` | 2 | 2 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder` | 2 | 1 | proof |
| `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison` | 2 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | 2 | 1 | proof |
| `WeilConjectures.ConstructibleSheaf.KernelCokernel` | 2 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | 2 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Gabber` | 2 | 4 | proof |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericConstancy` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangeGeometricPoints` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ZeroDimensionalSectionsStalks` | 3 | 1 | proof |
| `Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest` | 3 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | 3 | 1 | proof |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | 3 | 1 | proof |
| `Sheaf.Paper.InverseImageStalkGerm` | 4 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction` | 5 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleColimitCocone` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleFilteredData` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteSelection` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange` | 5 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleMayerVietorisModuleExactSegment` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1` | 5 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedCohomologyColimit` | 5 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` | 5 | 3 | proof |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | 5 | 4 | proof |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit` | 6 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleValuedInjectiveCohomology` | 6 | 1 | proof |
| `Sheaf.CategoryTheory.SiteCechMathlibComparison` | 6 | 1 | proof |
| `Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic` | 6 | 1 | proof |
| `Sheaf.Topology.IrreducibleIntegerExtensionVanishing` | 6 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` | 6 | 6 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion` | 7 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison` | 7 | 1 | proof |
| `Sheaf.CategoryTheory.SiteCechComplex` | 7 | 14 | proof |
| `Sheaf.Topology.ClosedUnionCohomologyVanishing` | 7 | 1 | proof |
| `Sheaf.Topology.CohomologyReductionConstantSubsheaves` | 7 | 1 | proof |
| `Sheaf.Topology.ConstantSubsheafFiniteFiltration` | 7 | 1 | proof |
| `Sheaf.Topology.ClosedImmersionPushforwardCohomology` | 8 | 1 | proof |

Waiting, not claimable: 1 modules whose proof uses a node that has no Lean declaration yet.

| module | distance to a target | sorry |
|---|---|---|
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | 3 | 4 |
