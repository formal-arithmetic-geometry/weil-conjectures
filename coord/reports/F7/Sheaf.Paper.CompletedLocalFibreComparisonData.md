## What changed

Filled both proof holes in `lean/Sheaf/Paper/CompletedLocalFibreComparisonData.lean`.
`WeilConjectures.ClassicalLocalFrobenius.stageLift_existsUnique` constructs its components
by scalar extension of `ULift.moduleEquiv.symm`. Naturality and the specified pure-tensor
formula hold on tensor generators; the same generators prove uniqueness.
`WeilConjectures.ClassicalLocalFrobenius.finitePullObject` applies the object clause of
`commonStageDerivedPullback_existsUnique` to the included pair `(E,K)`.
Scoped transparency-respecting elaboration options on `pinnedModels` and `pinnedStage`
prevent aggressive unfolding of their large pinning predicate. Their bodies stay unchanged.
These implement the existing declaration docstrings without changing the route,
signatures, definitions, imports, or unit realization.

## Proved and sorry left

Closed 2 of 2 existing holes:

- `WeilConjectures.ClassicalLocalFrobenius.stageLift_existsUnique`.
- `WeilConjectures.ClassicalLocalFrobenius.finitePullObject`.

No holes remain in the item; no holes or split statements were added.
The latter proof uses the existing, still postponed common-stage functor specification
from `Sheaf.Paper.DerivedPullbackTensorHom`; its proof remains a separate item.
Both declarations retain their attachment to
`def-zl-completed-local-fibre-comparison-data`.

## No longer needed

None. All three existing public imports supply definitions occurring in this module.
No dependencies, modules, or unit steps are bypassed, and no proof imports were added.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The definition node has no numbered proof plan;
the two existing theorem docstrings give the arguments implemented here.

Validation: both proofs compile on the server in 39.9 seconds. Scoped unused-section-variable
linter options preserve the existing implicit parameters without warnings. The earlier
transient server disk-space failure cleared on the next version.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
