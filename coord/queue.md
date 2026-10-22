# Work queue

42 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (4 clusters, 266 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/QCohTensorResolutionComparisonNaturality.lean:1:0: error: import Sheaf.Algebra.Homology.KFlatResolution failed, environment alrea |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 53, stage 3 1 items.

## Stage 1: nodes to split (8)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-proper-wcontractible-closed-fibre-rigidity` | 2008 | none |
| `lem-sfb-affine-profinite-family-serre-cd` | 2009 | none |
| `lem-sfb-tame-snc-quotient-resolution` | 4012 | none |
| `lem-sfb-equivariant-nodal-smooth-pair-resolution` | 4013 | none |
| `lem-sfb-equivariant-plurinodal-field-alteration` | 4013 | none |
| `lem-sfb-ramified-cartier-supported-purity` | 4013 | none |
| `lem-sfb-norm-completion-positive-cohomology-mono` | 4014 | none |
| `def-per-support-condition` | - | none |

## Stage 2: nodes to state (6)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-pe-internal-module-sectionwise-short-exact` | 1 | state | 0 |
| `lem-sfb-admissible-finite-type-field-quotient` | 1 | state | 0 |
| `lem-sfb-cech-vanishing-surjective-unions` | 1 | state | 0 |
| `lem-sfb-common-field-semilinear-induction` | 1 | state | 0 |
| `lem-sfb-galois-component-presentation` | 1 | state | 0 |

Not open yet: 369 nodes that below a finished node, not needed, 87 nodes that wait for a statement dependency (bottom-up), 7 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (19)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 1 | disputed | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | proof | route |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 2 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 9 | proof | route |
| `Sheaf.Paper.CompletedTowerPullback` | 5 | 3 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 5 | 10 | proof | route |
| `Sheaf.Paper.RingedProjectionLocalModel` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompletedCoefficientDirectImageDiagrams` | 6 | 1 | proof | route |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 4 | proof | route |
| `Sheaf.Paper.PbcScalarExtension` | 6 | 8 | proof | route |
| `Sheaf.Paper.CompletedIntegralQuotientModelComparison` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralPrincipalConeLocalCriterion` | 7 | 1 | proof | route |
| `Sheaf.Paper.RingedProjectionTensorShifts` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.RingedDerivedIdentityComparison` | 15 | 1 | proof | route |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | 8 | 1 | proof | 5 |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 1 | proof | 6 |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | - | 1 | proof | 7 |

## Stage 3: held for an open upstream PR (2)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
