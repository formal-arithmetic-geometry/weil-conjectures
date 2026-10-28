## Reason

The `beta_natural_evaluation` proof has two independent conjuncts. The
naturality conjunct is proved in the item; the evaluation conjunct is a
strictly smaller lower obligation needed by the same blueprint step.

## Old

The item module had no public declaration for the isolated evaluation clause;
`beta_natural_evaluation` was a single six-hole theorem.

## New

The item module adds `beta_evaluation_compatibility` with the exact evaluation
conjunct statement and records it as DAG node
`new-lem-pur-beta-evaluation-compatibility`.

## Users

The only user is `beta_natural_evaluation` in the same module, which combines
the lower theorem with its proved naturality conjunct. Existing downstream
modules retain their interfaces.

## Status

Required stage-3 decomposition; the lower theorem intentionally remains a
named `sorry` for a subsequent worker.
