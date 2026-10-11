# Work queue

17 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (2)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lemma-weil-pbc-stein-connectedness` | 2005 | rests_on_sorry |
| `thm-weil-pbc-stein-inputs` | 2006 | sorry_here |

## Stage 2: nodes to state (5)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-nagata-relative-gluing-datum-descent` | 2 | state | 7 |
| `lem-sc-boundary-cech-injective-middle` | 1 | state | 1 |
| `lem-sc-hilb-dominating-power` | 1 | state | 0 |
| `lem-sc-qcoh-complex-alternating-cech-derived-sections` | 1 | state | 0 |
| `lem-weil-pbc-locally-constant-zero-locus-clopen` | 1 | state | 0 |

Not open yet: 42 nodes that wait for stage 1, 6 nodes that wait for a statement dependency.

## Stage 3: modules to prove (10)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | 0 | 2 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange` | 1 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | 2 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion` | 3 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | 3 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` | 5 | 3 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` | 6 | 6 | proof |
