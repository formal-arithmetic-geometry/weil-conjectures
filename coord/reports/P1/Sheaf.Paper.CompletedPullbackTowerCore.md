## What changed

Restored the complete quarantined module, retaining all 51 public declarations and
all existing signatures and definition bodies. Proved the finite evaluation
comparison by transporting the existing
`purSequenceOrdinaryFactorization` tensor comparison along uniqueness of left
adjoints; its transpose equation is exactly the required limit projection. Proved
`WeilConjectures.pullbackTensorRoosModel_existsUnique` from the existing normalized
exact-products Roos comparison. Private helpers identify the negative and positive
Roos fibres using the arrow isomorphism `(id, -id)` and check that its cone map
preserves the ordinary-limit inclusion with zero second coordinate. The existing
comparison then supplies existence with the required K-injective normalization.
The existing private `integralOperationsExactProducts` lemma supplies exact
products for the precise completed-coefficient category without rebuilding its
universe-sensitive ring-sheaf arguments.
Naturality along a K-injective resolution proves uniqueness.

The new imports are proof-only. No target statement or mathematical definition changes.
The complete delivered module compiled through `lcompile.py` in 22.4 seconds.
The separate finite-evaluation proof also compiled in 6.4 seconds during development.

## Proved and sorry left

Closed two of the four original holes:

- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`.
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`.

Two existing holes remain, both attached to
`def-pur-completed-pullback-tower-core` and with their original source and proof docstrings:

- `WeilConjectures.pullbackTensorReductionModel_existsUnique`.
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`.

No new holes or split-off statements.

## No longer needed

No imports, public declarations, modules or nodes are withdrawn. The following
planned dependencies are unused by the replaced proof steps:

- `lem-coef-derived-system-evaluation-calculus`
  (`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`): neither new proof needs the
  derived coefficient-reduction calculus. Finite evaluation uses the ordinary
  adjunction comparison; Roos uses exact products and the normalized comparison.
- `def-a1-integral-finite-pullback-tower`
  (`Sheaf.Paper.IntegralOperationsWellDefined`): neither new proof uses finite
  pullback towers. That module remains needed for the Roos functor itself.
- `def-sf-strict-roos-functor`
  (`Sheaf.Paper.IntegralOperationsWellDefined`): unused by finite evaluation,
  retained and used by the Roos proof.

These dependencies remain attached to the two unfinished constructions or to the
existing statements. No node or module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The item source was initially absent from `lean/`; its rework row preserves it at
`quarantine/Sheaf/Paper/CompletedPullbackTowerCore.lean`. The entire archived source
was restored in the sandbox. The old Roos proof plan was mathematically valid but
missed the already proved `ExactProductsRoos.comparisonIso` API. That API uses
`-(1-s)`, so its sign must be changed while preserving the kernel inclusion;
applying it without that check would not establish the stated normalization.

The exact-products comparison is used as a proved categorical tool. The unit record
`sk-def-purity-conv` has no realized proof steps, and its statement and route are unchanged.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
