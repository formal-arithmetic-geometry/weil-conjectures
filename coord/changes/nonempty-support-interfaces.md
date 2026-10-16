# Nonempty support intermediate interfaces

## Reason

The target proof requires two substantial steps that are absent from the DAG:
construction of open/closed localization data and descent/gluing of the extension
class. They are exposed as named public theorems so each can be proved independently.
The returned delivery additionally required each theorem to be in its own module and
required the DAG statements and proof route to describe the exact signatures.

## Old

The module `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` contained both
intermediate declarations and the target declaration. The helper node records pointed
to that single module and used abbreviated statements and one-step proof text.

## New

`exists_nonempty_support_open_closed_models` is declared in
`Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed`; its node preserves
the exact Lean signature and records the open/closed construction proof plan.
`glue_nonempty_support_open_closed_models` is declared in
`Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing`; its node preserves
the exact Lean signature and records finite-stage extension-class descent. The target
module imports both helper modules and applies them in sequence.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | imports the target module; sees the target declaration |

## Status

landed 20261016T015248-L-721921 2026-10-16 (merge of deliver/F3/Sheaf.Paper.CondensedStratumModelInductionStepNonempty)
