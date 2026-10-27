## What changed

Restored the quarantined `Sheaf.CategoryTheory.FiniteCoconeLimits` module and repaired
`CategoryTheory.BigradedExactCouple.finiteCocone_limits` for the upstream definition of
`IsRegular`: use eventual boundary equality `hB`, rather than cycle equality `hZ`.
The theorem signature, public imports, limiting-subobject construction and other
proof steps remain unchanged. Updated the existing node's proof text accordingly.

## Proved and sorry left

This is an assigned repair with zero original holes. The repaired declaration is
`CategoryTheory.BigradedExactCouple.finiteCocone_limits`
(node `lem-sp-finite-cocone-limits`). Holes closed: zero. Holes added: zero.
Remaining holes in the delivered module: zero. No statements were split off.
The repaired module and the unchanged quarantined direct consumer
`Sheaf.CategoryTheory.FiniteCoconeExactCouple` compile cleanly through `lcompile.py`.
`#print axioms` for `finiteCocone_limits` and the consumer theorem
`finiteCocone_weakConvergence` reports only `propext`, `Classical.choice` and
`Quot.sound`. The consumer check used a scratch copy; it is not part of the delivery.

## No longer needed

None. Both imports and all existing statement and proof dependencies remain needed.
The module and its Lean attachment are restored, with no withdrawals or pruning.
The quarantined direct consumer `Sheaf.CategoryTheory.FiniteCoconeExactCouple`
continues to use the same theorem signature.

## Where the brief, the DAG or earlier work was wrong

The upstream sync changed `BigradedExactCouple.IsRegular` to eventual constancy of
boundaries. The quarantined proof and its node still supplied eventual cycle equality.
The existing `finiteCocone_stationary` theorem proves both equalities, so selecting
its boundary clause repairs the mismatch without changing any definition or statement.
The preserved historical docstring also describes regularity using cycles; the
current upstream definition and this report specify the boundary convention.

Repair record: `coord/changes/finite-cocone-limits-boundary-regularity.md`.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
