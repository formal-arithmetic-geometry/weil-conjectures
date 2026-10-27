## What changed

The ordinary scalar tower coherence theorem is now assembled from three named component propositions. Three public proposition definitions record the pullback, tensor, and internal-Hom clauses, and the parent theorem constructs its unchanged conjunction from the three component theorems.

## Proved and sorry left

Closed `scalarOperationsOrdinary_tower` by a direct constructor from its three component theorems. Added the following strictly smaller component theorems, whose proofs remain `sorry` for parallel follow-up: `scalarOperationsOrdinary_tower_pullback`, `scalarOperationsOrdinary_tower_tensor`, and `scalarOperationsOrdinary_tower_hom`. The module's pre-existing holes remain in `scalarPullbackLevel_existsUnique`, `scalarPullbackTower_existsUnique`, `scalarTensorLevel_existsUnique`, `scalarTensorTower_existsUnique`, `scalarPullbackOrdinary_existsUnique`, `scalarTensorOrdinary_existsUnique`, `scalarCompletion_existsUnique`, `scalarOrdinaryTensorChain_existsUnique`, and `scalarHomOrdinary_isIso`.

## No longer needed

None. No imports or declared dependencies were pruned. The interface change is recorded in `coord/changes/integral-operations-scalar-comparisons.md`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled three independent ordinary tower equalities into one large theorem. The Lean proof now exposes those exact clauses as separate named statements so they can be proved independently while preserving the target conjunction and its signature.

## New nodes

- `lem-pur-integral-operations-scalar-extension-pullback-clause`
- `lem-pur-integral-operations-scalar-extension-tensor-clause`
- `lem-pur-integral-operations-scalar-extension-hom-clause`

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
