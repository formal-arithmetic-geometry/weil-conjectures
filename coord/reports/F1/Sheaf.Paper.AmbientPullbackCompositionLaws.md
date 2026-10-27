## What changed

The target theorem is now proved by a real conjunction assembly.  Two new proof-only
modules split the ordinary Modules clauses from the derived localization clauses, and
the target imports them and assembles their six conclusions in the order required by
`CompositionLaws`.  The parent DAG node now records these two component statements as
its proof route.

## Proved and sorry left

Closed `WeilConjectures.AmbientPullbackTensor.pullback_compositionLaws`, the one original
sorry in this item.  Added the following two strictly smaller named statements, each
with one documented sorry for the corresponding remaining proof work:

- `WeilConjectures.AmbientPullbackTensor.ordinary_pullback_compositionLaws`
- `WeilConjectures.AmbientPullbackTensor.derived_pullback_compositionLaws`

Thus one upper sorry was closed and two lower component sorries were split off.

## No longer needed

No existing import was removed.  The generic semilinear compositor and generic
adjunction-normalization modules were inspected but are not needed by this route and
were not imported.  The original ambient site, mate, and localization dependencies
remain recorded on the two component nodes for their future proofs.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundled the ordinary section/mate calculation and the derived
exact-localization calculation into one theorem, although the available declarations
separate these arguments.  Splitting at that boundary gives two strictly smaller
statements while preserving the exact target statement and all six endpoint transport
terms.  No hypothesis or conclusion of `CompositionLaws` was changed.

## New nodes

- `new-lem-sf-ambient-pullback-ordinary-composition-laws`
- `new-lem-sf-ambient-pullback-derived-composition-laws`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AmbientPullbackCompositionLaws": "7f16387c2823c52b71d11566fc319662f47ef068", "Sheaf.Paper.AmbientPullbackDerivedCompositionLaws": "74b4497b91b5924cc640d8008f3e484f423cf0cf", "Sheaf.Paper.AmbientPullbackOrdinaryCompositionLaws": "79f6b1687b977c840c978b58321e12d4eb82df7d"}, "results": {}, "time": "2026-10-28T06:29:46+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
