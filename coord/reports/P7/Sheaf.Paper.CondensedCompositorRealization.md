## What changed

Restored the condensed compositor proof packet for the rework assignment. The
construction layer is in `CondensedCompositorRealizationData`, and the final
`condensedCompositorRealization` theorem now assembles its seven `Laws` fields
from four strictly smaller named theorem statements. The quarantined lower
shriek composition definition is restored in `RestoredLowerShriekComposition`
using the live compactification, proper, and open interchange APIs. The direct
imports that caused the red build are removed from the item module.

## Proved and sorry left

Closed the original item theorem
`WeilConjectures.CondensedCompositorRealization.condensedCompositorRealization`.
Added four strictly smaller theorem statements, each with a documented proof
plan and one `sorry`:

- `condensedCompositorIntegralLaws` (integral invertibility and naturality);
- `condensedCompositorRealizationSquare` (the realization square);
- `condensedCompositorSystemIndependence` (independence of the system word);
- `condensedCompositorIntegralRefinement` (the integral refinement equation).

The construction data and restored lower-shriek composition contain no `sorry`.
The delivery closes 1 of the original 1 item sorries and splits off 4.

## No longer needed

The item no longer directly imports `FiniteRingConstructibleDerivedOrigin`,
`TowerAdjointCompositorRealization`, `EtaleProEtaleCoefficientCompatibility`,
or `FiniteAdjointCompositorTransposes`; the declarations remain available in
the library. The proof packet also avoids the original direct import of the
quarantined `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`.
No declared mathematical dependency below the unit route is removed; the data
module retains the APIs used by the construction definitions and helper proofs.

## Where the brief, the DAG or earlier work was wrong

The rework row identifies a red build caused by unavailable direct imports.
The earlier monolithic source restored those imports after a rollback, even
though its final theorem was still admitted. The extraction packet is the
compatible repair: it preserves all public construction signatures and moves
the unfinished composition obligations into strictly smaller named statements.
No target statement was changed, and no statement was judged false.

## New nodes

- `def-pur-condensed-compositor-realization-data`
- `def-pur-restored-lower-shriek-composition`
- `lem-pur-condensed-compositor-integral-laws`
- `lem-pur-condensed-compositor-integral-refinement`
- `lem-pur-condensed-compositor-realization-square`
- `lem-pur-condensed-compositor-system-independence`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CondensedCompositorIntegralLaws": "20b936e3ad2b126b53e7ee6679113e826d53b04a", "Sheaf.Paper.CondensedCompositorIntegralRefinement": "bed48a075d0d0814398ee4e462fcc21b06599c75", "Sheaf.Paper.CondensedCompositorRealization": "f3c1e919f021fb3cdb00a8632b9769a75da95541", "Sheaf.Paper.CondensedCompositorRealizationData": "34ea50fa9bdabdbc7da1978dc343ad7ca5d1e26c", "Sheaf.Paper.CondensedCompositorRealizationSquare": "e3186c1b28171ea2655f06c3eb4fb103ac186cb7", "Sheaf.Paper.CondensedCompositorSystemIndependence": "96aa1011abeb2cfef878047d0f4669028f1019b0", "Sheaf.Paper.RestoredLowerShriekComposition": "9418c35a38a3a54419127877fbbec589afdda3b0"}, "results": {}, "time": "2026-10-28T03:57:45+0800", "transitive": 0, "version": 1}
```

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
