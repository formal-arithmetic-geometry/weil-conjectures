## What changed

Added `Sheaf.Paper.CompactSupportRealizedScalarTransposeProjection`, a new intermediate
statement for the realized proper/open scalar transpose after postcomposition with the
inverse target reduction projection. The assigned module now imports this intermediate
and proves its original theorem by cancellation with that isomorphism. The intermediate
proof remains the single split-off `sorry`; the assigned theorem itself is proved by Lean.

## Proved and sorry left

Proved `WeilConjectures.sfCompactSupportRealizedScalarTranspose` by applying
`cancel_mono` to the inverse of the target finite reduction isomorphism and the new
projection-normalized equation.

One sorry remains in `WeilConjectures.sfCompactSupportRealizedScalarTransposeProjection`.
It is the geometric proper/open mate calculation before the final target projection,
with node `lem-sf-compact-support-realized-scalar-transpose-projection`.

## No longer needed

No existing proof-dependency imports were removed. The proof uses the compact-support
coefficient action and system-operation realization imports through the new intermediate.
No DAG nodes or modules beyond the split intermediate were pruned.

## Where the brief, the DAG or earlier work was wrong

The rework row records a global-build failure caused by the restored dependency chain's
bad imports. The assigned theorem's original module still had one genuine proof hole; no
statement correction was needed. The DAG proof plan describes the full proper/open mate
calculation but does not expose its projection-normalized pre-cancellation equation, so
that strict intermediate was added.

## New nodes

`lem-sf-compact-support-realized-scalar-transpose-projection` records the postcomposed
transpose equation used by the assigned theorem. Its Lean declaration is in
`Sheaf.Paper.CompactSupportRealizedScalarTransposeProjection` and its proof is left as the
single named stage-3 split described above.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportRealizedScalarTranspose": "2def7613542ff16270232fc23e16acc1f2203727", "Sheaf.Paper.CompactSupportRealizedScalarTransposeProjection": "b7e805dec530b1dd2168503b98d957b8c8eea1e5"}, "results": {}, "time": "2026-10-28T01:08:12+0800", "transitive": 0, "version": 1}
```

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
