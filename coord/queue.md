# Work queue

55 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (5)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-strict-local-exchange` | 1003 | sorry_here |
| `lemma-weil-pbc-smooth-curve-artin-schreier` | 1007 | sorry_here |
| `lemma-weil-pbc-smooth-curve-kummer-localization` | 1007 | sorry_here |
| `lemma-weil-pbc-stein-connectedness` | 2006 | rests_on_sorry |
| `thm-weil-pbc-stein-inputs` | 2007 | sorry_here |

## Stage 2: nodes to state (5)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-nagata-relative-gluing-datum-descent` | 2 | state | 7 |
| `lem-sc-boundary-cech-injective-middle` | 1 | state | 1 |
| `lem-sc-hilb-dominating-power` | 1 | state | 0 |
| `lem-sc-qcoh-complex-alternating-cech-derived-sections` | 1 | state | 0 |
| `lem-weil-pbc-locally-constant-zero-locus-clopen` | 1 | state | 0 |

Not open yet: 42 nodes that wait for stage 1, 6 nodes that wait for a statement dependency.

## Stage 3: modules to prove (45)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` | 1 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | 1 | 6 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit` | 2 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections` | 2 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | 2 | 1 | proof |
| `WeilConjectures.ConstructibleSheaf.KernelCokernel` | 2 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | 2 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Gabber` | 2 | 5 | proof |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangePointsFibrePoint` | 3 | 1 | proof |
| `Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest` | 3 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | 3 | 1 | proof |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineLocalAcyclicOpenRestriction` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClassCore` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleMayerVietorisModuleVanishing` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackIsoTorsionColimit` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPullback` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleAcyclicEffacementLadder` | 5 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` | 5 | 3 | proof |
| `Sheaf.AlgebraicGeometry.ModuleAcyclicUnderlyingSections` | 6 | 1 | proof |
| `Sheaf.Topology.FiniteClosedCoverCohomologyVanishing` | 6 | 1 | proof |
| `Sheaf.Topology.IrreducibleIntegerExtensionVanishing` | 6 | 1 | proof |
| `Sheaf.Topology.NoetherianExtensionByZeroReduction` | 6 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` | 6 | 6 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback` | 7 | 1 | proof |
| `Sheaf.Topology.AbelianOpenExtensionByZero` | 7 | 1 | proof |
| `Sheaf.Topology.AbelianOpenExtensionByZeroStalks` | 7 | 1 | proof |
| `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf` | 8 | 6 | proof |
| `Sheaf.CategoryTheory.ExtensionByZeroPresheaf` | 9 | 7 | proof |

Waiting, not claimable: 1 modules whose proof uses a node that has no Lean declaration yet.

| module | distance to a target | sorry |
|---|---|---|
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | 3 | 4 |
