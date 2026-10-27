## What changed

Filled `refinementRestriction_data_isIso` using the componentwise criterion
`NatTrans.isIso_iff_isIso_app`. The component equality hypothesis rewrites each
component to `refinementRestriction`; the geometric component invertibility is
recorded as the strictly smaller split-off theorem
`refinementRestriction_component_isIso` in a new module.

The item DAG node now records the actual proof dependency on that component node.

## Proved and sorry left

- Proved: `WeilConjectures.PurCompactSupport.refinementRestriction_data_isIso`.
- One sorry split off: `WeilConjectures.PurCompactSupport.refinementRestriction_component_isIso`,
  node `lem-sf-refinement-open-restriction-is-iso-components`.

## No longer needed

The parent proof no longer directly depends on the shift and mate nodes
`lem-pur-exact-adjunction-unit-shift-descent`,
`lem-sp-canonical-right-derived-adjunction-shift`, and
`lem-weil-pbc-commshift-nattrans-comp-whisker`; those belong to the separate
shift theorem. The parent proof also does not import any of the geometric
component-calculation modules directly; they remain dependencies of the
split-off component theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundled component invertibility, natural-transformation
extensionality, and shift material into one theorem. The available declarations
support the categorical extensionality step directly, while the clopen
component calculation is a separate geometric obligation. The proof is therefore
split at that strictly smaller component statement.

## New nodes

`lem-sf-refinement-open-restriction-is-iso-components` records the componentwise
isomorphism needed by the parent theorem, with its geometric proof dependencies.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RefinementOpenRestrictionComponentIsIso": "3bc2b6d6b5cf1dab8aa318ca3100ed546a0566f5", "Sheaf.Paper.RefinementOpenRestrictionIsIso": "3d4af1304cfd3b24625da66db79b7dc042dd2c57"}, "results": {}, "time": "2026-10-28T04:09:49+0800", "transitive": 0, "version": 1}
```

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
