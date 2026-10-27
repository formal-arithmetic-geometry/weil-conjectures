## What changed

Marked `etaleCofinalSupport_composition` as `STATEMENT-DISPUTED` after inspecting its hypotheses and the `CofinalSupport` structure. No proof was added because the statement is not determined by the supplied data.

## Proved and sorry left

No holes were closed. The existing `sorry` in `AlgebraicGeometry.Etale.SystemProjection.etaleCofinalSupport_composition` remains, with node `lem-pur-etale-cofinal-support-composition`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The node claims that coefficient projection invertibility and its cocycle imply coherence of the normalized support comparisons. However, `CofinalSupport` stores `compositionX`, `compositionY`, and each `h` independently. Its `normalization` field constrains each individual `h` through `q`, `factorX`, `factorY`, and `kappa`, but imposes no equation connecting `h (s.trans r)` with `h r`, `h s`, or the `compositionX`/`compositionY` fields. The conclusion varies with those unconstrained composition fields while `hi` and `hq` remain unchanged. A coherence hypothesis (or an additional structure field fixing the ordinary/derived composition comparison) is required before this theorem can be proved.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleCofinalSupportComposition": "d2ae51ded6245ae05e64853c053aaae9d1ecbaea"}, "results": {}, "time": "2026-10-28T00:45:35+0800", "transitive": 0, "version": 1}
```

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
