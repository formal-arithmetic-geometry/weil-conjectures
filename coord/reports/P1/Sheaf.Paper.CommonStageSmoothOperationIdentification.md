## What changed

Added two intermediate statement modules. `CommonStageSmoothOperationCore` isolates the
operation witnesses, comparison isomorphisms, representative and transport equations.
`CommonStageSmoothOperationShift` isolates the shift, exactness, transformation, and
finite-stage shift equations. The target module imports these modules and combines their
conclusions into `Result`.

## Proved and sorry left

The target declaration `commonStageSmoothOperationIdentification` is proved by explicit
existential assembly from the two intermediate statements. Two strictly smaller public
statements remain with `sorry`: `commonStageSmoothOperationCore` and
`commonStageSmoothOperationShift`.

## No longer needed

The target proof no longer directly uses the original detailed proof-plan dependencies;
its Lean proof uses only the two new intermediate modules. The prior top-level tool-use
approvals are therefore removed from the sandbox copy of the target node. The target's
statement and all imported statement definitions are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan expands a long coefficient-transport calculation that cannot be
closed from the available declarations in this item. The reduction separates the genuine
operation/transport obligation from the independent shift/exactness obligation; no
statement was weakened.

## New nodes

`lem-pur-common-stage-smooth-operation-core` records the operation and transport
intermediate. `lem-pur-common-stage-smooth-operation-shift` records the shift and
exactness intermediate. Both have matching Lean modules and node records in the sandbox.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
