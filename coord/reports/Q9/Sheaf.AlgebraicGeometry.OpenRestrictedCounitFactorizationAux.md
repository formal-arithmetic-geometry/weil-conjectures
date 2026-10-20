## What changed

Retire `Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux` in favor of
`WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux`.
The copy is listed in `deleted.txt`; its DAG node
`new-open-restricted-counit-compatibility-aux` now records the existing official
declaration and module. Only the node's `lean` field changes. The change record
is `coord/changes/retire-open-restricted-counit-factorization-aux-Q9.md`.

For the rework, restored the complete quarantined source in the sandbox and
removed only the redundant command
`attribute [local irreducible] derivedPullback`. The resulting source equals
the official twin after its copyright header. All declarations and proofs are
preserved by the official module. The final retirement packet withdraws the
copy; the repaired text remains in `scratchpad/` for inspection. The quarantine
archive and upstream files were not edited.

The named Sheaf consumer is already absent. Its official counterpart already
imports the official auxiliary and uses the same declaration, so no consumer
edit is needed. Verification probes are excluded from delivery by deliver3.py.

## Proved and sorry left

Actual item holes: zero. Holes closed: zero of zero. Holes added: zero.
Split off: zero. No remaining `sorry` declarations are introduced or retained
in the item or its official replacement.

The existing complete proofs of
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_compatibility_aux`
and
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_factorization`
are preserved. Fresh remote checks through `lcompile.py`:

- Official auxiliary import and axiom check: exit 0, 1.9 seconds.
- Full current official consumer source and axiom check: exit 0, 6.2 seconds.
- Restored source with temporary Lean profiling: exit 0, 52.9 seconds;
  the only warning requests removal of that development option.

The temporary profiler was removed. Two clean restored-source rechecks hit
60 seconds; profiling identified type checking (34.5 seconds cumulatively)
and linting (49.1 seconds cumulatively, including nested work) as the cost.
The inherited attempt had compiled the same clean repaired text in 44.8
seconds. This final packet contains no restored source or profiler option:
the explicit retirement uses the already compiled official twin, whose proof
and consumer passed the current checks above.

Both axiom checks report exactly `propext`, `Classical.choice`, `Quot.sound`.
No statement or definition changed, and no proof was replaced by a hole.

## No longer needed

Retired module: `Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux`.
No current Lean source, including quarantined consumers, imports this copy.
Its listed consumer `Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorization`
is already absent; the official counterpart already uses the twin.

No mathematical dependency or DAG node is pruned. The original statement,
proof steps, `proof_deps`, and unit route are retained. There are no current DAG
parents citing this auxiliary node, and the unit has no realization attached
to the copy that requires migration. No new nodes are added.

## Where the brief, the DAG or earlier work was wrong

The retirement inventory names two Sheaf paths that are already absent from
`lean/`. The auxiliary survives in quarantine, and its DAG attachment still
named the missing copy. The official twin already contains the exact required
reducibility repair.

The initial required dry run reproduced the earlier absent-deletion rejection.
The delivery tool has since gained explicit support for withdrawal of a
quarantined module using its original Lean path in `deleted.txt`. This packet
uses that supported route. No launcher script, budget, claim, target, or shared
source was changed by this worker.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
