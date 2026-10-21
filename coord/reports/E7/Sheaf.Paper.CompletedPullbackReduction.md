## What changed

Proved
`AlgebraicGeometry.Scheme.completedReductionTargetTransition_exists` in
`lean/Sheaf/Paper/CompletedPullbackReduction.lean`. The proof forms the natural
cochain computation of each finite target, inverts its components on K-flat
representatives, and descends the ordinary quotient transformation through the
fully faithful restriction to resolving representatives. Its component equation
is exactly the existing normalization predicate; full faithfulness proves uniqueness.

Added proved private helpers for this descent and its composite-functor interface,
for the natural finite computation, and for its invertibility. A proof-local essentially-small instance fixes the
site and coefficient universes. The private imports of `AdicCoefficientDatum` and
`ReductionPullbackDerivedTower` expose their existing internal counit and resolving
whiskering constructions. Existing public imports, declarations, signatures, and
non-proof definition bodies are unchanged. No other module is adapted.
The existing node records the proved auxiliary transition argument and retains all steps of the unfinished main proof.

## Proved and sorry left

Closed one of five original holes:
`AlgebraicGeometry.Scheme.completedReductionTargetTransition_exists`.
Added zero holes and split off zero statements.

Four original holes remain unchanged, all attached to
`lemma-weil-pbc-completed-pullback-reduction` (with the finite-interface constructions
also recorded by `def-cbc-completed-reduction-finite-interfaces`):

- `AlgebraicGeometry.Scheme.completedReductionOrdinaryComparison_exists`.
- `AlgebraicGeometry.Scheme.completedReductionFiniteEvaluation_exists`.
- `AlgebraicGeometry.Scheme.completedReductionOrdinaryTransition_exists`.
- `AlgebraicGeometry.Scheme.completedPullback_reduction`.

The derived transition proof uses the existing ordinary transition, whose proof
remains one of the listed original obligations. No assertion of axiom-free closure
of the main completed-pullback theorem is made.

## No longer needed

Removed unused private proof imports:
`StrictPerfectPackageOnSite`, `ConstantCompletionEquivalence`,
`RingedKoszulCompletionReflector`, `RingedStrictTowerHomotopyLimit`,
`ProjectionFormulaTotalization`, `AdicCompletionReduction`, and
`WeilCompletedTensorReflector`, plus the redundant direct imports
`CompleteCoefficientDatum`, `ProjectionFormulaArrows`, `KFlatCoefficientUniverse`,
`IntrinsicCompletionCompleted`, `PbcFiniteCompletedCoefficientMap`,
`ProEtaleProjectionFormulaArrows`, and
`RingedTopoiCanonicalTensorPullbackOfUniverses`. The public imports and two proof
imports exposing the counit and resolving-class interfaces provide all used APIs.
No mathematical node or module is withdrawn. The new descent proof uses neither
strict-tower normalization nor completed-constant scalar comparison. Those remain
in the planned proof of the untouched main theorem, so they are not declared pruned.

## Where the brief, the DAG or earlier work was wrong

The listed strict-tower and normalization proof dependencies cannot presently be
imported by this module: `PulledReductionStrictTowerComparison`,
`PulledReductionNormalizationComparison`, and `OrderedExchangeCoefficientComparison`
reach `PbcQbarCompletedPullback`, then `PbcConstructibleReductionPullback`, then
`SbcCompletedOperations`, whose private imports include this item. Their current
holders are respectively M1, E9, K9, and M9 for `SbcCompletedOperations`.
No held module was changed to remove that cycle. This does not affect the proved
transition-existence obligation, which uses the independent resolving-class API.

The derived computation must use `pbcExtensionCounit`, exactly as
`completedReductionFiniteModelMap` does. Replacing it by the independently recorded
`reductionDerivedCounit` does not establish the specified normalization by
conversion. The delivery preserves the original specified map and proves its
normalization without changing either counit.

The earlier missing `CompletedTowerPullback.olean.server` artifact is available.
The final module compiles without warnings through `lcompile.py` in 29.2 seconds;
the site-size instance is confined to the proved theorem.
The retained direct specialization caused a kernel timeout: conversion expanded
concrete composite pullback functors while comparing component formulas. The
proved generic `completedReduction_descend_composite` interface retains the
component equation with abstract functors, so specialization no longer needs
that expensive conversion. No timeout or heartbeat limit is increased, no public
definition changes, and no file is split to avoid the limit.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
