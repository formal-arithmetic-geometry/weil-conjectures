# Work queue

30 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (1 clusters, 2338 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor` | 2338 | WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.SubalgebraLimit | error: Sheaf/AlgebraicGeometry/EtaleSumExtensionTensor.lean: bad import 'Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality' |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 31, stage 3 169 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 301 nodes that below a finished node, not needed, 85 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (29)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` | - | 7 | proof | 2 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SignedDoubleHomCone` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | - | 3 | proof | 3 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SignedFibreTriangulated` | - | 1 | proof | 3 |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.PositiveProductRadius` | - | 1 | proof | 3 |
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
| `Sheaf.AlgebraicGeometry.PurityClopenAffineLineFiniteType` | - | 1 | proof | 5 |
| `Sheaf.RingTheory.PowerSeries.ExpSubstHom` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.NaturalTransportPowers` | - | 1 | proof | 6 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement` | - | 1 | proof | 7 |
| `Sheaf.CategoryTheory.DualizableJointlyConservativeLocality` | - | 1 | proof | 7 |
| `Sheaf.Paper.EtaleLisseFiltrationDevissage` | - | 1 | proof | 10 |
| `Sheaf.RingTheory.ColimOfLocalizations` | - | 1 | proof | 13 |
| `Sheaf.Algebra.Homology.IntegerFlatRepresentative` | - | 1 | proof | 17 |
| `Sheaf.Algebra.Homology.FilteredPageLocalization` | - | 3 | proof | 20 |
| `Sheaf.Algebra.Homology.FilteredTensorGradedComparison` | - | 2 | proof | 20 |
| `Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized` | - | 1 | proof | 21 |

## Stage 3: held for an open upstream PR (2)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
