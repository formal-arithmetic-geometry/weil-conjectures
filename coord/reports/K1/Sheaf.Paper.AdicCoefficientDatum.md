## What changed

Filled fifteen existing theorem proofs in `lean/Sheaf/Paper/AdicCoefficientDatum.lean`.
All published signatures, visibility, definitions and public imports are unchanged.
The finite-ring comparison uses the sheafification comparison and local bijectivity.
The Grothendieck tower proof transports the existing small-diagram theorem across the
site and indexing equivalences. The derived tower proof verifies the two hypotheses
of the existing K-flat resolving-class theorem, using levelwise quasi-isomorphisms
and exact scalar restriction. Balancing existence reuses the already declared
`completedAdicBalance_exists`, with the same tensor normalization.

Proof-only imports provide module-sheaf colimits, the sheafification comparison and
the equivalence of module categories on the small site model. No consumer needs adaptation.

## Proved and sorry left

Original holes: 20. Holes closed: 15. Holes added: 0. No decomposition or split-off.
All declarations below are in `AlgebraicGeometry.Scheme`, except the first, which is
in `AlgebraicGeometry.Scheme.AdicCoefficients`.

Closed:

- `finiteRingComparison_exists`
- `reductionCoefficientMap_id`
- `reductionCoefficientMap_comp`
- `reductionTower_isGrothendieckAbelian`
- `completedReductionTowerMap_naturality`
- `completedReductionModuleTowerFunctor_additive`
- `completedReductionTower_exists`
- `reductionBalance_exists`
- `completedReductionProjection_comp`
- `completedTowerEvaluationStep_naturality`
- `reductionRestrict_preservesFiniteLimits`
- `reductionRestrict_preservesFiniteColimits`
- `completedReductionDerivedNormalization_isIso`
- `completedReductionTower_properties`
- `completedReductionEvaluation_isIso`

Remaining, unchanged named theorem holes, all attached to
`def-weil-pbc-adic-coefficient-datum`:

- `completedReductionTransition_exists`: construct and characterize the sheafified tensor transition.
- `reductionBalance_naturality`: tensor generation and functoriality of scalar extension.
- `reductionBalance_cocycle`: tensor generation and associativity of coefficient multiplication.
- `completedReductionDerivedNormalization_exists`: descend balancing using K-flat scalar extension.
- `completedReductionEvaluation_exists`: compare the universal derived pairs after evaluation.

## No longer needed

No original imports, nodes or modules are pruned. The proof follows the existing
node's small-site, K-flat resolution and universal-left-derived route.
No new scalar-extension balancing existence lemma is needed: the existing
`completedAdicBalance_exists` has exactly the required signature.
Exploratory imports of `Mathlib.Algebra.Category.Ring.FilteredColimits` and
`Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated` were removed; neither
is an additional dependency of the final proof.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy or assigned definition repair was found. The definition
node has no separate proof steps; its statement already contains the construction
and proof route used here. The original balancing existence hole duplicates the
normalized theorem in `CompletedAdicCoefficientDatum`, so its proof is direct reuse.
The remaining five original holes are left unchanged, as permitted for a module
with several holes; no new obligation is handed to another worker.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
