## What changed

Proved the six existing theorems of
`Sheaf.SixFunctors.IntegralExpressionOccurrences`, preserving all existing signatures,
definitions, attributes and imports. Added five proved private helpers for evaluation
under variable renaming, the corresponding occurrence-label equivalence, successful
searches, updates at absent labels, and evaluation along a successful search. Updated
the existing node's proof, proof_deps and proof_origin to describe these elementary
structural inductions. No other Lean module is changed.

Searches: LeanFinder found polynomial evaluation-under-renaming analogues, with no
result for this expression type. Loogle found the sum-update API and source inspection
found `Function.Bijective.sumMap`; the dependent update proof uses direct case splits
to retain the definitions' specified decidable-equality instances. Repository searches
found no alternative proofs of the expression-specific statements.

## Proved and sorry left

Closed 6 of 6 existing holes (namespace `WeilConjectures.IntegralSystemRealization`):

- `inputShift_obj`.
- `Expression.shiftOccurrenceFunctor_obj`.
- `Expression.slotContext_evaluate`.
- `Expression.independentInputs_bijectiveLabel`.
- `IndependentExpression.variableContext_isSome`.
- `IndependentExpression.variableContext_evaluate`.

All belong to node `def-pur-integral-expression-occurrences`.
Holes added: 0. Holes remaining in this delivery: 0. Split off: 0.

## No longer needed

None: no imports, nodes, or modules removed or withdrawn. The sole existing public
import supplies the expression and interpretation definitions used throughout. No
additional proof imports are needed, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof list despite containing six theorem holes;
its proof fields now record the structural arguments. Successful-search existence
requires only surjectivity, as the stronger private search characterization shows;
injectivity is needed later for evaluation of a single updated label. No statement
or definition repair was required.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
