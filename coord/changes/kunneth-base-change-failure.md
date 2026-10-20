## Reason

The target proof requires two new intermediate interfaces: conversion from the unbounded
predicate to the existing cyclic witness hypotheses, and descent from an algebraically
closed extension to the generic function field. The target module therefore imports two
new Sheaf modules.

## Old

The target module had one direct `sorry` and no helper modules. Its proof plan expanded the
full Stacks argument locally.

## New

The target proof calls `cumulative_and_not_universal_of_unbounded` and
`exists_functionField_descent_of_algClosedWitness`. Both declarations are recorded by
new DAG nodes and retain their own named proof obligations.

## Users

Only `Sheaf.AlgebraicGeometry.KunnethBaseChangeFailure` imports the new modules. Existing
source-library declarations and all other consumers are unchanged.

## Status

landed 20261020T211811-L-3503474 2026-10-20 (merge of deliver/P5/Sheaf.AlgebraicGeometry.KunnethBaseChangeFailure)
its statement is unchanged.
