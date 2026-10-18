## What changed

Added the strict existence substatement `adicUnit_exists_data` and proved the uniqueness half of `adicUnit_exists` by homological-complex extensionality and tensor-generator extensionality. The other existing holes remain unchanged.

## Proved and sorry left

Closed the uniqueness portion of `adicUnit_exists`; the existence data is split into `adicUnit_exists_data` and remains `sorry` with node `adic-unit-exists-data`. Existing sorries remain in `adicBalance_exists`, `adicTransitionComplex_exists`, `adicBalanceHom_naturality`, `adicTransitionComplex_naturality`, `adicNormalization_cocycle`, `adicNormalization_unit`, and `adicReductionUnderlying_tensor`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The direct construction of transition maps requires a mixed-universe comparison between nested scalar extension and restriction; the currently landed same-universe tensor comparison cannot instantiate on the pro-etale site. No existing statement was changed.

## New nodes

`adic-unit-exists-data` records the strict existence part of the identity-extension theorem; its proof is the sheafified tensor-unit construction from Stacks Tag 03EK.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
