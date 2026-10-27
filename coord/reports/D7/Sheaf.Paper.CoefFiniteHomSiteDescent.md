## What changed

Filled the target theorem `coefFiniteHomSiteDescent` by assembling two strictly smaller
named component theorems in the same module: `coefFiniteHomSiteDescent_descent` for
constructible descent and Tor interval transport, and
`coefFiniteHomSiteDescent_coherence` for the monoidal, symmetry, quotient, Hom-square,
and law-transport conclusions. The target proof is a direct conjunction of these two
component results. Existing imports and helper definitions are unchanged.

## Proved and sorry left

The target theorem `coefFiniteHomSiteDescent` is proved. Two component theorem holes are
left as the named decomposition:

- `coefFiniteHomSiteDescent_descent`, node
  `lem-coef-finite-hom-site-descent-core-descent`.
- `coefFiniteHomSiteDescent_coherence`, node
  `lem-coef-finite-hom-site-descent-core-coherence`.

Thus one upper sorry is closed and two strictly smaller sorries are added as a
proof decomposition.

## No longer needed

None. The established helper definitions and imports remain needed by the two component
statements and by downstream users of the target module.

## Where the brief, the DAG or earlier work was wrong

The seven-step proof plan was mathematically sound but too large to close in one
transaction. The target was therefore decomposed at the natural boundary between step 1
(descent and interval preservation) and steps 2--7 (scalar/site and Hom coherence). No
statement or definition was weakened.

## New nodes

`lem-coef-finite-hom-site-descent-core-descent` records the constructible descent component
and its source step 1. `lem-coef-finite-hom-site-descent-core-coherence` records the
remaining monoidal and Hom coherence component and its source steps 2--7.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.CoefFiniteHomSiteDescent": "d405bb124646ce1720fa53f8d3ea954a20e52b70"}, "results": {"Sheaf.Paper.CoefFiniteSiteHomTransport": {"hash": "25a7089419505644db4b0e43dac819a1a1a1de9d", "status": "OK"}, "Sheaf.Paper.FiniteCoefficientHomChange": {"hash": "6040c31ddad1fd61407da5e854c90f3fc5f5636b", "status": "OK"}, "Sheaf.Paper.FiniteReductionOfPurity": {"hash": "4620554d4463beb678ddc465f0cb6a592be1f51e", "status": "OK"}, "Sheaf.Paper.NormalizedSmoothOrientationUnits": {"hash": "33f1e2787018a3fa04fc9e87753cb2c3e43d4ced", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds": {"hash": "7626d3590cf3bc4e79653aa04822e4946e4c7c0c", "status": "OK"}}, "seconds": 130, "time": "2026-10-28T01:16:22+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
