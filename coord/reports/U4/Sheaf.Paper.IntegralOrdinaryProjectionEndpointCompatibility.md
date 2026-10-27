## What changed

Restored `Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData` to the current
V1-owned source, including its original two-field endpoint data structure.  The
compatibility module likewise retains its original public imports and theorem
signature.  The theorem declaration is marked `STATEMENT-DISPUTED` and its `sorry`
is retained because the stated data permits arbitrary endpoint isomorphisms.  The
compatibility node now includes
`lem-sf-ordinary-projection-endpoint-iso-data-q2` in `stmt_deps`, as required for the
`IntegralOrdinaryProjectionEndpointData` type used by the theorem.

## Proved and sorry left

No theorem was proved.  The sole `sorry`,
`WeilConjectures.integralOrdinaryProjection_endpointCompatibility`, remains and is
marked `STATEMENT-DISPUTED`: composing an arbitrary target endpoint isomorphism with
a nontrivial automorphism changes the right-hand side while preserving the data
fields.  The repair is handed to V1/the maintainer as requested by the return.

## No longer needed

No imports, declarations, or proof dependencies were removed in this repair.  The
previous unforced definition change and its change record were withdrawn.

## Where the brief, the DAG or earlier work was wrong

The endpoint compatibility statement is false for the data structure recorded by
`lem-sf-ordinary-projection-endpoint-iso-data-q2`: that structure stores only source
and target isomorphisms and asserts no relation between them.  The countervariation
`t ↦ t ≪≫ α` by a nontrivial automorphism `α` preserves the structure fields but
changes the displayed square.  Adding a compatibility field would change V1's
assigned endpoint-data obligation, so this delivery does not do that.  The original
split must be repaired by the maintainer/V1 or by correcting the statement and its
DAG `statement_change` under the project process.

## New nodes

No new nodes were created.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility": "06638ac18d8ac365d9241e9627f1caac17b94d64"}, "results": {}, "time": "2026-10-28T06:46:29+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
