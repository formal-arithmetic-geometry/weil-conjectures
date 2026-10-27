## What changed

Proved `WeilConjectures.PurCompactSupport.refinementRestriction_data_shift` by applying
`NatTrans.CommShift.of_core`, evaluating the shift square at each object, and rewriting
both components with the supplied component equation. Added the lower pointwise
component-shift statement in `Sheaf.Paper.RefinementRestrictionComponentShift` with its
own DAG node; its geometric calculation remains the single split `sorry`.

## Proved and sorry left

Closed the original `refinementRestriction_data_shift` `sorry`. Added one strictly lower
named statement, `refinementRestriction_component_shift`, whose proof is left as `sorry`.

## No longer needed

The upper proof directly uses only the new component-shift node and Mathlib's
`NatTrans.CommShift.of_core` assembly. The four original geometric nodes
`lem-sfb-proetale-open-restriction-counit`,
`lem-sf-proetale-open-pullback-preserves-kinjective`,
`lem-sfb-proetale-identified-open-closed`, and
`lem-weil-pbc-proetale-ringed-open-closed` are no longer needed by this route and are
removed from the target node's proof dependencies and imports. The split component
calculation retains the pullback-composition and derived-adjunction shift dependencies
that it explicitly plans to use.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the geometric component calculation and the categorical
extensionality step. The categorical step is short once the pointwise shift equation is
stated; the bundled plan did not expose that lower obligation as a separate Lean statement.

## New nodes

- `lem-sf-refinement-restriction-component-shift`: pointwise integer-shift compatibility
  of `refinementRestriction`, used by the delivered upper theorem.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RefinementOpenRestrictionShift": "4d1bfabe79ef4984fa85b6ee1f1736651ca5aa0e", "Sheaf.Paper.RefinementRestrictionComponentShift": "46feb963dff905cfe1254ca4743f1d12816cc252"}, "results": {"Sheaf.Paper.RefinementOpenRestriction": {"hash": "380a131577b6b214adc0dfa01534fd7a2fabe52c", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T07:06:29+0800", "transitive": 0, "version": 1}
```

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
