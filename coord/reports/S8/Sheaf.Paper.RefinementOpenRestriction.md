## What changed

The proof of `WeilConjectures.PurCompactSupport.exists_refinementRestriction` now
combines three strict intermediate statements: existence of the natural
transformation with the specified components, invertibility of any such
transformation, and its ordinary integer shift compatibility.  These statements
are in `RefinementOpenRestrictionData`, `RefinementOpenRestrictionIsIso`, and
`RefinementOpenRestrictionShift`; the item imports those modules privately.

## Proved and sorry left

The original `exists_refinementRestriction` hole is closed by applying the three
intermediate statements.  Three strictly smaller named theorem holes were added:
`refinementRestriction_data`, `refinementRestriction_data_isIso`, and
`refinementRestriction_data_shift`, with nodes
`lem-sf-refinement-open-restriction-data`,
`lem-sf-refinement-open-restriction-is-iso`, and
`lem-sf-refinement-open-restriction-shift`, respectively.

## No longer needed

No proof-dependency imports or DAG proof steps were pruned.  The original
component, clopen, and shift dependencies remain the stated source of the three
intermediate arguments.

## Where the brief, the DAG or earlier work was wrong

The existing module's single proof hole packages three logically independent
parts of the blueprint argument.  The DAG did not expose these as separate
Lean statements, so the proof was decomposed into the three strict subclaims
above.  The global build error recorded for this item was a stale bad-import
artifact from the rework batch; the current source and sandbox compile cleanly.

## New nodes

`lem-sf-refinement-open-restriction-data` records the component natural
transformation.  `lem-sf-refinement-open-restriction-is-iso` records its
invertibility from the component formula.  `lem-sf-refinement-open-restriction-shift`
records its ordinary integer shift compatibility.  Each node has a corresponding
module in this delivery and retains the original blueprint source and proof
dependencies.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RefinementOpenRestriction": "380a131577b6b214adc0dfa01534fd7a2fabe52c", "Sheaf.Paper.RefinementOpenRestrictionData": "fb81349314e1a0dde42ad78097c6a2f470c8a864", "Sheaf.Paper.RefinementOpenRestrictionIsIso": "ad8cec52399e24eb6b0da6a1f9f2faf434638618", "Sheaf.Paper.RefinementOpenRestrictionShift": "a3546541af8806a2568d0c4615c254fb54f99571"}, "results": {}, "time": "2026-10-28T00:50:18+0800", "transitive": 0, "version": 1}
```

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
