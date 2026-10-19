## What changed

Proved `Module.exists_elementary_generating_tuple_change` without changing its statement.
All additions are private, proved helpers in the assigned module. Elementary operations
are encoded as a finite list, with explicit inverses and preservation of the generated
submodule. The proof follows the original Nakayama/unit-pivot/quotient induction. It
inducts on the cardinality of a finite index type, removes the chosen pivot index,
lifts the quotient operations, and corrects differences using shears. Instead of
permuting the target tuple, it swaps the source pivot into the chosen target index.

Each operation defines a linear equivalence on scalar tuples, transported to an
invertible matrix through Mathlib's `Matrix.GeneralLinearGroup.toLin`. Its action on
arbitrary module tuples is checked on scalar coordinate vectors. Induction on the
operation list gives the reverse matrix product. Prefixes of that same list give
the required sequence indexed by natural numbers, so the matrices and intermediate
tuples are synchronized by construction.

Searches using LeanFinder and Loogle found no applicable general generating-tuple
result. Mathlib/source searches found matrix decomposition results requiring a field
and basis-change results requiring bases; neither replaces the local-ring argument.

## Proved and sorry left

Closed the original hole in `Module.exists_elementary_generating_tuple_change`
(node `lem-pur-local-generating-tuples`): 1 of 1 original holes proved.
Added holes: zero. Remaining holes: zero. Split-off statements: zero.
The private helpers, including `exists_tuple_ops`, `TupleOp.matrix_act`, and
`tupleRun_matrix`, are all proved. The empty tuple and zero module cases are covered
by the same induction; no freeness or minimality hypotheses were added.

## No longer needed

None. Both original proof imports are used: `Mathlib.RingTheory.LocalRing.Module`
for Nakayama and `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic` for the unit criterion.
All original declared proof dependencies remain needed. No new modules are imported,
and no nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No defect in the assigned statement or its six-step argument was found. The quotient
lifting step needs substantial finite-list bookkeeping, supplied here by private
proved helpers. The earlier interrupted sandbox drafts were discarded; no draft
intermediate modules are included in this delivery. No definition or interface changes
and no consumer adaptations are needed.

Preflight conservatively classified the section-local `variable` and `omit` commands
of the private helpers as an interface change. Their scope ends before the original
public theorem, whose full signature is unchanged. The direct importers need no
adaptation. This is documented in
`coord/changes/B4-local-generating-tuples-private-helper-scopes.md`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
