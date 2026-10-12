# Work queue

43 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (5)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-strict-local-exchange` | 1003 | sorry_here |
| `lemma-weil-pbc-smooth-curve-artin-schreier` | 1006 | sorry_here |
| `lemma-weil-pbc-smooth-curve-kummer-localization` | 1006 | sorry_here |
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

## Stage 3: modules to prove (33)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | 1 | 7 | proof |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit` | 2 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero` | 2 | 4 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangePoints` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections` | 2 | 1 | proof |
| `Sheaf.Paper.ZeroDimensionalCohomology` | 2 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | 2 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | 2 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCoverRestrictionBound` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrimeInjectiveCohomologyComparison` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackIsoPrimeTorsionDevissage` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | 3 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | 3 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClassCore` | 4 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPullback` | 4 | 6 | proof |
| `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf` | 4 | 3 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` | 5 | 3 | proof |
| `Sheaf.Topology.InverseImageModule` | 5 | 2 | proof |
| `Sheaf.Topology.NoetherianVanishingByIrreducibleComponents` | 5 | 2 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` | 5 | 3 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` | 6 | 6 | proof |

Waiting, not claimable: 1 modules whose proof uses a node that has no Lean declaration yet.

| module | distance to a target | sorry |
|---|---|---|
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | 4 | 4 |
