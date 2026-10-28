## What changed

Copied the assigned module into the F9 sandbox and marked the theorem statement as
`STATEMENT-DISPUTED`. No imports or declarations were otherwise changed.

## Proved and sorry left

No holes were closed. The existing `WeilConjectures.PurCompactSupport.restriction_commShift`
hole remains, with its original `sorry`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The statement assumes four arbitrary `Functor.CommShift` structures, but gives no
compatibility between the shift structures on the two sides of `restriction a c`.
For an isomorphism `e : F ≅ G`, Mathlib's `Functor.CommShift.ofIso_compatibility`
proves `NatTrans.CommShift e.hom` only for the transported shift structure on `G`.
The theorem requires the independently supplied composite structure on
`image S c ⋙ pbcDerivedRestrict (a.map Y)`, and Lean reports these as distinct
class arguments. In general coherent shift structures are not unique, so an
arbitrary natural isomorphism need not commute with both choices. The source-level
claim requires canonical shift instances or an explicit compatibility hypothesis.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralCompactSupportRestrictionShift": "e671b037ca3702c103802252b664a20de009d5ba"}, "results": {}, "time": "2026-10-28T08:02:48+0800", "transitive": 0, "version": 1}
```

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
