## What changed

The item now assembles both parent conclusions from strictly simpler named statements.
`inverseEvaluation_existsUnique` is assembled from separate existence and uniqueness
statements. `completedPrimitiveCounitComparison` is assembled from separate Roos
realization existence and fixed-realization comparison existence statements. The
existing `directEvaluation_eq` proof is unchanged.

## Proved and sorry left

Closed:

- `WeilConjectures.PrimitiveCounit.inverseEvaluation_existsUnique`.
- `WeilConjectures.completedPrimitiveCounitComparison`.

Split off as remaining holes:

- `WeilConjectures.PrimitiveCounit.inverseEvaluation_exists`.
- `WeilConjectures.PrimitiveCounit.inverseEvaluation_unique`.
- `WeilConjectures.completedPrimitiveCounit_roos_exists`.
- `WeilConjectures.completedPrimitiveCounit_comparisons_exists`.

## No longer needed

No imports were removed. The parent proof metadata no longer needs the former
long proof route directly: its actual proof uses the four split statements above.
The existing declarations and imports remain because they define the public
interfaces used by those statements and by the item module.

## Where the brief, the DAG or earlier work was wrong

The lower statements use `PrimitiveCounit.RoosRealization` and
`PrimitiveCounit.Comparisons`, which are declared in this item module. Moving them
to separate modules would make the item import its own lower-module declarations
through a cycle unless the whole interface block were relocated. The strictly
simpler statements therefore remain in this module, while receiving their own DAG
nodes and being used by real assembly proofs. The previous DAG proof described a
long construction that was not completed in this session; the parent node now
records the actual decomposition.

## New nodes

- `lem-pur-completed-primitive-counit-evaluation-existence`
- `lem-pur-completed-primitive-counit-evaluation-uniqueness`
- `lem-pur-completed-primitive-counit-roos-realization-existence`
- `lem-pur-completed-primitive-counit-comparisons-existence`

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
