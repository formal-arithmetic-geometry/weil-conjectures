## What changed

Updated `Sheaf.Paper.FiniteLevelProjectionFactors`. The conjunction theorem
`FiniteLevelComparison.proper_adjunction_comparison` is now proved by conjunction
introduction from two named component statements, `proper_adjunction_comparison_unit`
and `proper_adjunction_comparison_counit`. Those component statements preserve the
unit and counit equations exactly and are recorded as new DAG nodes. No imports or
existing definitions were changed.

## Proved and sorry left

Closed one sorry: `FiniteLevelComparison.proper_adjunction_comparison`.

Two strictly smaller component statements were added with sorry proofs:
`FiniteLevelComparison.proper_adjunction_comparison_unit`
(`new-sp-proper-adjunction-unit`) and
`FiniteLevelComparison.proper_adjunction_comparison_counit`
(`new-sp-proper-adjunction-counit`). The original remaining six sorries are
`FiniteLevelComparison.monoidal_existsUnique`,
`FiniteLevelComparison.pushMap_existsUnique`,
`FiniteLevelComparison.open_adjunction_comparison`,
`FiniteLevelComparison.proper_projection_comparison`,
`FiniteLevelComparison.open_projection_comparison`, and
`FiniteLevelComparison.coefficient_models`.

## No longer needed

None. All existing imports and proof dependencies remain needed by the retained
route; the parent node now additionally uses the two split component nodes.

## Where the brief, the DAG or earlier work was wrong

The parent node treated the proper adjunction comparison's conjunction as one
unresolved step. The Lean proof naturally decomposes it into independent unit and
counit equations, so the DAG now records those two strictly smaller obligations.

## New nodes

`new-sp-proper-adjunction-unit` records the unit component equation.

`new-sp-proper-adjunction-counit` records the counit component equation.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
