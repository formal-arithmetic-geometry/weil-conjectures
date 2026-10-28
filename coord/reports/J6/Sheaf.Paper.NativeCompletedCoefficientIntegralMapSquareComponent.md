## What changed

Replaced the sorry in Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquareComponent
by a proof from the existing coefficient presentation data. Private proved helpers
compare finite constant sections, identify normalized integral residues with continuous
reduction, and identify completed direct image with conjugated continuous precomposition.
Adjunction and the pointwise native normalization then give the required component.
Only the assigned module and its proof-plan node change. The public theorem statement
and public import are unchanged. No shared definition or upstream source is changed.

## Proved and sorry left

Closed one hole: WeilConjectures.LocallyFiniteAdicCompactSupport.
coefficient_presentation_integralMap_pull_square_component
(node lem-sf-native-completed-coefficient-integral-map-square-component).
No sorry remains in the assigned module. No holes or split-off statements are added.
All private helpers are proved. The argument uses existing statements as permitted by
stage 3; it does not claim that their entire transitive dependency closure is sorry-free.

## No longer needed

None of the original imports or three declared dependencies is pruned: each contributes
actual presentation, native normalization, or completed pullback data to the proof.
No module is withdrawn and no unit route changes. No localization existence or
presentation-existence theorem is needed: the supplied presentations suffice.

## Where the brief, the DAG or earlier work was wrong

The planned finite-projection argument is valid, but the projections are on the
completed coefficient sheaf, not on the native target. The proof first characterizes
the completed direct-image map by those projections and then uses adjunction to
compare the native-valued maps pointwise. This supplies the previously omitted glue
without splitting the same obligation again. The DAG proof now records these steps.
The latest unit statement is retained; its realized statement and steps are empty,
and this delivery changes no unit record.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquareComponent": "938ed0e6a4b4c4b9e31fb1d8fd6f76a433e0eca8"}, "results": {"Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquare": {"hash": "4445e2771a3333a315a50e37aa1fe63d857186ca", "status": "OK"}}, "seconds": 87, "time": "2026-10-28T12:04:44+0800", "transitive": 0, "version": 1}
```

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
