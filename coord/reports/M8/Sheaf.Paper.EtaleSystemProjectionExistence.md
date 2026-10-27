## What changed

The theorem `AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjection_nonempty`
was completed by assembling two strictly smaller construction records. The delivery adds
`Sheaf.Paper.EtaleSystemProjectionBasicData` for ordinary supports, evaluations, and scalar
models, and `Sheaf.Paper.EtaleSystemProjectionComparisonData` for the normalized comparison
fields. The item imports those private proof modules; no existing public statement or
source-library module was changed.

## Proved and sorry left

The original hole in `etaleSystemProjectionTheory_nonempty` is closed. Two strictly smaller
construction obligations remain as named public theorems with their own nodes:
`etaleSystemProjectionBasicData_nonempty` and
`etaleSystemProjectionComparisonData_nonempty`. Each is a genuine component of the
construction and neither restates `Nonempty (Theory c l)`.

## No longer needed

No proof dependency is removed from the blueprint route. The item now uses the two new
component nodes directly; their statements use the original sequence-site, scalar-adjunction,
and derived-pushforward dependencies. No existing module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original item bundled ordinary operations and all mate-normalized comparisons into one
large record, which cannot be constructed directly from the currently available interfaces.
The proof plan is therefore split into the ordinary operation record and the comparison record,
then combined by a real record constructor. This preserves the unit route and leaves each
unproved statement strictly simpler than the target.

## New nodes

`lem-pur-etale-system-projection-basic-data` attaches
`Sheaf.Paper.EtaleSystemProjectionBasicData` and records existence of the ordinary operation
fields. `lem-pur-etale-system-projection-comparison-data` attaches
`Sheaf.Paper.EtaleSystemProjectionComparisonData` and records existence of all comparison
fields for a fixed ordinary choice. No change record is required.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleSystemProjectionBasicData": "7c7a4c25d619ca453c2d1af554c4cdb3a6cacad8", "Sheaf.Paper.EtaleSystemProjectionComparisonData": "ee94efec2ec32017d42e69e20600888a5d24582e", "Sheaf.Paper.EtaleSystemProjectionExistence": "43d883007d6a93184073cdf7b64b0fa364525bf3"}, "results": {}, "time": "2026-10-28T00:49:10+0800", "transitive": 0, "version": 1}
```

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
