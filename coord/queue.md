# Work queue

21 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (0 clusters, 2337 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.


Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 31, stage 3 573 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 301 nodes that below a finished node, not needed, 85 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (21)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.RelativeProjExists` | 10 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus` | 4 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit` | 4 | 1 | proof | route |
| `Sheaf.Paper.ProjectionFormulaArrows` | 4 | 6 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars` | 6 | 2 | proof | route |
| `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` | 6 | 7 | proof | 2 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | 6 | 1 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` | 7 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SignedDoubleHomCone` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | 7 | 3 | proof | 3 |
| `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` | 7 | 2 | proof | 3 |
| `Sheaf.CategoryTheory.SignedFibreTriangulated` | 12 | 1 | proof | 3 |
| `Sheaf.FieldTheory.BertiniFieldExtension` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.InvertibleTensorScalarExtension` | 9 | 1 | proof | 4 |
| `Sheaf.Paper.KFlatConeComparison` | 9 | 1 | proof | 4 |
| `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` | 9 | 4 | proof | 4 |
| `Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge` | 13 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.StandardGroupSchemes` | - | 12 | proof | 4 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | 15 | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement` | - | 1 | proof | 7 |

## Stage 3: waiting for statements of dependencies (17)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.SmoothPurity.NormalizedWitness` | 1 | 1 | `lem-pur-condensed-exceptional-reconstruction` |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | 5 | 1 | `def-pur-affine-space-comparison` |
| `Sheaf.Paper.FiniteReductionOfPurity` | 5 | 8 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.FiniteTorStability` | 5 | 15 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.SixFunctors.RationalOperations` | 5 | 1 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | 6 | 12 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.DualizingObjectPurity` | 6 | 1 | `lem-pur-projection-purity-agreement` |
| `Sheaf.Paper.PurityCompositionCoherence` | 6 | 12 | `lem-pur-diagonal-dnc-chart-normalization` |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | 6 | 8 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.Paper.DlConstructibleFibresExact` | 8 | 1 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | 10 | 4 | `det-sp-tower-gamma` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | 13 | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.FiniteFreeCompactComposition` | - | 8 | `lem-pur-system-level-projection-formula-coherence` |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | - | 1 | `lem-pur-vector-integration-site-comparison` |
| `Sheaf.Paper.RationalPurityPresentation` | - | 13 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.VerdierExchange` | - | 1 | `sk-thm-sf-tensor-hom` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 8 | `lem-pur-adic-purity-scalar-naturality` |

## Stage 3: held for an open upstream PR (11)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | bundle/sec-smooth-purity-d2,prove2/sk-prop-sf-kunneth-ordinary |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
