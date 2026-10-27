## What changed

Added `Sheaf.SixFunctors.RationalVerdierIntegralCocycle`, which packages the
integral comparison cocycle for the three ordinary Verdier tensor presentations.
The item module remains at its original rational composition statement and keeps
its original proof hole.

## Proved and sorry left

Proved `WeilConjectures.RationalVerdier.integral_comparison_cocycle`.
The item theorem `WeilConjectures.RationalVerdier.extension_composition_equation`
remains one `sorry`, recorded by the existing node
`lem-coef-rational-verdier-composition-equation`. No new `sorry` was added.

## No longer needed

None. The integral cocycle module imports only the project declarations used by
its proof.

## Where the brief, the DAG or earlier work was wrong

None.

## New nodes

`lem-coef-rational-verdier-integral-cocycle` records the strictly lower
integral-coherence step used before rational localization.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierCompositionEquation": "fb5fccba0b48c197ef64532bc9ec5041001ab0b9", "Sheaf.SixFunctors.RationalVerdierIntegralCocycle": "48aebd5fae7a6017fa48ea37dab860dd63de4f90"}, "results": {}, "time": "2026-10-28T06:51:08+0800", "transitive": 0, "version": 1}
```

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
