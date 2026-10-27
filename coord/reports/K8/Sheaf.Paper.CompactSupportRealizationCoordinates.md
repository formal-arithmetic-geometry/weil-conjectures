## What changed

Closed the uniqueness hole in
`WeilConjectures.CompactSupportFactorNormalization.ordinaryRestrictionSquare_existsUnique`
by obtaining an identity-on-sections square from the new existence theorem and using
section extensionality for uniqueness. Added the public helper module
`Sheaf.Paper.CompactSupportRealizationSquareExistence`, whose existence theorem is the
strictly smaller split-off obligation. Removed unused proof-only `import all` lines
from that helper. The parent and helper compile together in import order.

## Proved and sorry left

Closed 1 original sorry: `ordinaryRestrictionSquare_existsUnique`.

Added 1 strictly smaller sorry: `WeilConjectures.CompactSupportFactorNormalization.ordinaryRestrictionSquare_exists`
(in `Sheaf.Paper.CompactSupportRealizationSquareExistence`, node
`lem-zl-compact-support-realization-square-existence`). Its statement is only the
existence and identity-on-sections part; the parent supplies the complete uniqueness
argument.

## No longer needed

Removed the helper's unused `import all Sheaf.AlgebraicGeometry.ProEtaleOperations`
and `import all Sheaf.Paper.CompactSupportCondensedRealization` imports. The ordinary
restriction construction still uses the five public imports retained in the helper.
No existing DAG dependency node is withdrawn, and the parent unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan conflated existence of the normalized coefficient square with
its uniqueness. The existing section law makes uniqueness a short independent
argument, so the existence half is recorded as a separate node rather than repeating
the full target statement. No target statement or existing definition was changed.

## New nodes

Added `lem-zl-compact-support-realization-square-existence`, with a source-level
identity-on-sections construction as the remaining proof obligation. Its Lean module
is `lean/Sheaf/Paper/CompactSupportRealizationSquareExistence.lean`; the node's
`proof_deps` record the coefficient, completed-support, and pro-etale operation
interfaces used by the construction.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportRealizationCoordinates": "ec1e3d9d8189498a7914c78a24551e47aff3af5d", "Sheaf.Paper.CompactSupportRealizationSquareExistence": "54b412aa91b41affb6501cab84182600c82e0d1e"}, "results": {}, "time": "2026-10-28T04:46:59+0800", "transitive": 0, "version": 1}
```

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
