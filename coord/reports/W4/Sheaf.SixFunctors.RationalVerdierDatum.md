## What changed

Restored `Sheaf.SixFunctors.RationalVerdierDatum` against the current
`RationalVerdierModels` interface and removed three unused proof imports. The theorem
`WeilConjectures.RationalVerdier.datum_exists` now composes the existing integral Verdier
conclusion with two genuine lower steps: K-flat coefficient localization and descent of
signed-symmetry naturality through K-flat resolutions. Added
`Sheaf.SixFunctors.RationalVerdierDatumFromIntegral` and
`Sheaf.SixFunctors.RationalVerdierDatumNaturality`.

## Proved and sorry left

`datum_exists` is proved by a real three-step composition in the item module. Two
strictly smaller public obligations remain:

- `datum_of_integral_kflat` in `RationalVerdierDatumFromIntegral`, node
  `lem-coef-rational-verdier-datum-kflat`;
- `datum_naturality_of_kflat` in `RationalVerdierDatumNaturality`, node
  `lem-coef-rational-verdier-datum-naturality`.

No definition contains a sorry.

## No longer needed

Removed the unused imports `Sheaf.Paper.IntegralResidueTor`,
`Sheaf.Paper.PbcRationalTransport`, and
`Sheaf.Paper.IntegralOperationsPreserveConstructible` from the item module. The lower
K-flat theorem retains the mathematical localization route through the public model
interface; no mathematical node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The rework row records a stale bad-import failure: the current published interface is
`RationalVerdierModels`, and the restored module compiles against it. The original item
node bundled the integral Verdier construction, K-flat localization, and roof descent;
the DAG copy now records these as separate proof steps and lower nodes.

## New nodes

`lem-coef-rational-verdier-datum-kflat` records the rational datum and signed-symmetry
naturality on K-flat chain representatives.

`lem-coef-rational-verdier-datum-naturality` records the independent descent from those
representatives to arbitrary derived maps.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierDatum": "164615386e1467e18c23406d7a9b67282fff944c", "Sheaf.SixFunctors.RationalVerdierDatumFromIntegral": "579e9c9f3616523c42730f4de1948ac87502ea3d", "Sheaf.SixFunctors.RationalVerdierDatumNaturality": "c3b6396d049c71aba6431754e2e1d6abadbc4337"}, "results": {"Sheaf.SixFunctors.RationalVerdier": {"hash": "62aa3761695accb0a49fd85e0ff1a1b1e659896e", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T00:58:39+0800", "transitive": 0, "version": 1}
```

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
