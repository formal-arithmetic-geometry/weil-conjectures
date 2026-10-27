## What changed

The assigned transport-pasting theorem now constructs its record from three named
single-field obligations. Added the vertical, horizontal, and base-change modules,
with proof-only imports in the item module. The three obligations remain explicit
named theorem holes because the supplied `gamma` has no compatibility hypothesis.

## Proved and sorry left

Proved `WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransportPasting`
by assembling the three fields. Three strictly simpler field obligations remain sorry:

- `integralSystemProperOpenTransportPastingVertical`;
- `integralSystemProperOpenTransportPastingHorizontal`;
- `integralSystemProperOpenTransportPastingBaseChange`.

Thus one upper sorry is closed and three lower sorries are added.

## No longer needed

None. The original operations, realization-data, and semilinear-pasting dependencies
remain the stated source of the three split obligations.

## Where the brief, the DAG or earlier work was wrong

The module's existing `STATEMENT-DISPUTED` note is correct: arbitrary `gamma` is not
constrained to be the bridge-transported gamma, so the displayed equations cannot be
derived from the supplied data alone. The DAG's single proof step therefore had to be
decomposed into its three field equations. No target statement was changed.

## New nodes

Added `lem-sf-integral-system-proper-open-transport-pasting-vertical`,
`lem-sf-integral-system-proper-open-transport-pasting-horizontal`, and
`lem-sf-integral-system-proper-open-transport-pasting-basechange`, each matching one
field and carrying the corresponding named theorem hole.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting": "43349615e0cbf7a738088e5f9ba2b3fac6ab983d", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingBaseChange": "37edd9f74bb6a409bccaf2492ac2575ec4522f75", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingHorizontal": "21181c3aa741237e2f1028904ae0da575a08d4c3", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingVertical": "87c8e33c6cb2fdba6d85feaee84af7ace794f847"}, "results": {}, "time": "2026-10-28T05:07:08+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
