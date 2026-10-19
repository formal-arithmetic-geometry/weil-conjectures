## What changed

Proved all six theorem holes of `Sheaf.SixFunctors.IntegralExpressionOccurrences`.
The single-component shift agrees pointwise with dependent function update; the
occurrence specialization applies that equality. Structural induction proves
slot-context evaluation, bijectivity of independent leaf labels, successful label
search, and evaluation of the unique-label context.

Private, fully proved helpers establish evaluation under renaming, the occurrence
equivalence under renaming, the label-search criterion, invariance under changes
away from leaf labels, and evaluation along a successful unique-label search.
No existing statement, definition, public visibility, or import changed.

## Proved and sorry left

Closed six original holes (all in node `def-pur-integral-expression-occurrences`):

- `WeilConjectures.IntegralSystemRealization.inputShift_obj`.
- `WeilConjectures.IntegralSystemRealization.Expression.shiftOccurrenceFunctor_obj`.
- `WeilConjectures.IntegralSystemRealization.Expression.slotContext_evaluate`.
- `WeilConjectures.IntegralSystemRealization.Expression.independentInputs_bijectiveLabel`.
- `WeilConjectures.IntegralSystemRealization.IndependentExpression.variableContext_isSome`.
- `WeilConjectures.IntegralSystemRealization.IndependentExpression.variableContext_evaluate`.

Holes added: zero. Holes left: zero. Split off: zero.
Single-file compilation succeeds. The proof covers each expression constructor;
the tensor cases distinguish both summands and use label injectivity to exclude
updates to the other subtree. No nonemptiness assumption on the label type is
introduced; label search uses exactly the existing surjectivity hypothesis.

## No longer needed

None. The only import, `Sheaf.SixFunctors.IntegralSystemExpressionDomain`, supplies
the existing statement types and is retained. The node has no planned proof
dependencies to prune, and no additional module is imported. No unit route changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The node is a definition node with no numbered
proof plan; the six theorem docstrings supply the structural induction arguments
implemented here. Searches recorded in `searches.jsonl` found no shorter existing
expression-specific theorem. Previous interrupted work had only unresolved
contradiction branches, now closed by simplifying failed Option searches.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
