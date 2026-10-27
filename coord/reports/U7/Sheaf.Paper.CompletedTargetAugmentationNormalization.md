## What changed

Proved both declarations in `Sheaf.Paper.CompletedTargetAugmentationNormalization`,
with their statements unchanged. Identify the published reduction/pullback comparison
with the uniquely normalized stratum comparison and use its augmentation equation.
Reuse `AdicCoefficientDatum.towerProjection_properties` for the direct-image unit
identity. Functoriality, the inverse reduction comparison, and naturality of the
specified `directImageRlimIso` give the third identity. Both square identifications
are definitional equalities. No completeness of ordinary pullback or direct image
is used, and no projection or completion map is inverted.

Updated the item's DAG proof and dependency list to this shorter existing API route.
Removed redundant imports; retained the protected ringed tower-limit comparison
proof import and three public imports that provide the statements'
actual objects and maps. No existing declaration, definition, or theorem signature
was changed, and no consumer adaptation is needed (no current Lean module directly
imports this item).

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.completedTargetAugmentationNormalization`.
- `AlgebraicGeometry.Scheme.completedTargetAugmentationNormalization_square`.

Zero holes added, zero holes left in the delivery, and no split-off statements.
The final pruned module compiled cleanly through `lcompile.py` (9.3 seconds).
A source comparison confirms both theorem signatures are unchanged; the updated
DAG route has no dependency cycle through this item.
The proofs use existing named library results; they do not claim that all of those
results' transitive dependencies are already sorry-free.

## No longer needed

Removed direct imports:

- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.
- `Sheaf.Paper.CompletedRlimFunctor`.
- `Sheaf.Paper.ReductionPullbackDerivedTower`.
- `Sheaf.Paper.AugmentedDiagramProjectionMate`.
- `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.

The general profinite-coefficient, exact-operation, reduction/pullback,
constant-tower normalization, augmented-projection, and ringed tower-limit
normalization arguments need not be replayed in this module. Accordingly removed
these direct proof dependencies from its node:

- `lem-weil-pbc-profinite-coefficient-inverse-image`.
- `def-weil-pbc-proetale-operations`.
- `lem-weil-pbc-reduction-pullback-derived-tower`.
- `lem-weil-pbc-constant-tower-pushforward-normalization`.
- `lem-weil-pbc-augmented-diagram-projection-mate`.

The protected `RingedTowerPushforwardLimitComparison` unit-route import and its
node remain, even though naturality is exposed by the scheme-specific natural
isomorphism.

Their results may remain transitively needed by the retained API modules; none is
withdrawn or declared globally unused. The removed adic-datum, Rlim, square, and
finite-witness direct imports remain available through retained public imports.
The Qbar completed-pullback module supplies no declaration used by these statements
or proofs. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan did not account for the existing scheme-specific normalized completion-unit
identity in `towerProjection_properties`. Its second equation can be used directly.
The reduction comparison's public uniqueness theorem also identifies it with the
published stratum comparison, so the first equation needs no new derived model.
No mathematical statement was found false. The original `def-weil-pbc-completed-pullback`
Lean attachment points to the Qbar interface; this item's actual maps are the
integral `CompletedPullback` / `CompletedPullbackInterface` constructions already
publicly reexported by `CompletedDirectImageLimits`.

Public-import pruning is recorded in
`coord/changes/U7-completed-target-augmentation-imports.md`.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
