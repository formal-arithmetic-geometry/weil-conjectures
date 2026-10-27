## What changed

Proved `WeilConjectures.IntegralSystemRealization.IndependentExpression.reductionContext_evaluate`
in `Sheaf.SixFunctors.IntegralOperationShiftData`. Apply the existing
`IndependentExpression.variableContext_evaluate`, then identify the two input
families by dependent function extensionality. At the selected label both are
reduction of the replacement; elsewhere both are reduction of the original input.
The sandbox module compiled successfully through lcompile.py (31.2 seconds).
All public signatures, definitions, attributes and imports are unchanged.
This is a partial delivery of a module with several holes.

## Proved and sorry left

Closed one of the four original holes:
`WeilConjectures.IntegralSystemRealization.IndependentExpression.reductionContext_evaluate`.

Three original holes remain, all attached to `def-pur-integral-operation-shift-data`:

- `WeilConjectures.IntegralSystemRealization.tensorShifts_existsUnique`.
- `WeilConjectures.IntegralSystemRealization.IndependentExpression.shift_naturality`.
- `WeilConjectures.IntegralSystemRealization.limitShift_roos`.

Added zero holes and split off zero statements. The remaining holes and their
existing source citations and proof docstrings are untouched.

## No longer needed

None. No imports, modules or nodes are removed. The completed identity directly
uses the already imported `IntegralExpressionOccurrences` context-evaluation
identity and the definition of `inputReduction` from `IntegralSystemExpressionDomain`.
The remaining declarations continue to require their recorded dependencies.

## Where the brief, the DAG or earlier work was wrong

No discrepancy established. The item's node has an empty proof field because
it describes a definition interface with several attached proof obligations.
The completed proof is precisely the pointwise argument already given in its
existing declaration docstring. No dependency or route change is needed.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
