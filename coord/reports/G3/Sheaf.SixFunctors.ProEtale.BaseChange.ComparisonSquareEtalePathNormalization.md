## What changed

Restored the quarantined module
`Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization`.
Replaced the removed `Etale.pullbackSquareComparison_def` reference with direct
unfolding. Generalized the private `plus_square_expansion` and `square_restrict`
helpers to `CommSq`, expanding the ordinary comparison in the restriction identity.
Moved the final algebraic combination into a proved private `normalization_aux`
with a variable square-component morphism, then specialized it at the actual
component and `sq.toCommSq`. This avoids kernel normalization caused by converting
between the original square and the projection of a rebuilt Cartesian square.
The exported theorem signature and docstring, all imports and file-local commands,
and the two declared DAG dependencies are unchanged.

Updated the DAG proof and origin note to match. Change record:
`coord/changes/G3-etale-path-normalization-sync-repair.md`.

## Proved and sorry left

Zero-hole repair. The archived source had 0 textual sorries; the delivered source
has 0. `AlgebraicGeometry.ProEtale.comparisonSquareEtalePath_normalization` and every
private helper are fully proved. Holes closed: 0. Holes added: 0. Sorries left: none.
Split off: none. No axiom or new public declaration was introduced.

The complete repaired module compiled in 7.8 seconds before final cleanup.
The public signature was compared verbatim with the quarantine archive; all lines
satisfy the 100-character limit. Final source compiled in 10.3 seconds; the unchanged archived direct consumer
`ComparisonSquareTransport` compiled against it in 6.6 seconds. The temporary consumer
copy was removed from the delivery after validation.

## No longer needed

No imports, nodes, or modules were pruned. `ComparisonSquarePaths` and
`Sheaf.Paper.DerivedSquarePasting` remain needed. The obsolete private
`etale_square_expansion` helper is removed: the restriction theorem now states the
ordinary square comparison in expanded form. The unavailable upstream helper name
`Etale.pullbackSquareComparison_def` is no longer used.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole upstream-sync repair, as recorded in `coord/rework.tsv`.
Replacing the missing lemma alone exposed a second issue: the old final proof
caused a deterministic kernel timeout when converting commutative-square arguments
inside the concrete comparison. The repair uses the existing definitions unchanged,
with a restriction theorem whose square argument matches the final component exactly.
The mathematical route and the unit route are preserved. No upstream caching attribute
is restored or altered. The quarantined source and its Lean attachment remain intact.

The normal downstream checker cannot traverse the absent quarantined item. Searches
of live and quarantined sources identify `ComparisonSquareTransport` as the sole direct
consumer; the change record also lists all five dependents named by the rework table.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
