## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.second_projection_interchange` in
`Sheaf.Paper.RationalP1SecondProjectionInterchange`. The proof imports two new
proof-only modules. `RationalP1SecondProjectionInterchangeCore` introduces the
constructed `secondTraceStrengthTail` and isolates generic shifted-strength
naturality; `RationalP1SecondProjectionInterchangeTail` isolates cancellation of
the fixed projection tail. The item proof applies the first theorem and then
whiskers the second theorem by the outside arrow.

## Proved and sorry left

The item hole `second_projection_interchange` is closed. Two strictly simpler
intermediate theorem holes remain, each with a matching DAG node:

- `secondTraceStrength_naturality` in
  `Sheaf.Paper.RationalP1SecondProjectionInterchangeCore`;
- `second_projection_tail_cancellation` in
  `Sheaf.Paper.RationalP1SecondProjectionInterchangeTail`.

No definition contains `sorry`; `secondTraceStrengthTail` is a concrete
associator, braiding, and tensor-shift composite.

## No longer needed

The original planned proof dependencies
`lem-sfb-ringed-projection-tensor-composition`,
`lem-pd-module-ringed-topos-derived-comparison`, `sk-def-sp-tate-twist`, and
`def-sfb-rational-tate-pullback-comparison` are not used by the delivered route.
The fixed route uses the existing pretrace-data and second-pull-comparison
interfaces through the two new split theorems. No existing import was removed.

## Where the brief, the DAG or earlier work was wrong

The original node treated the full arbitrary-arrow identity as one monolithic
coherence calculation. The actual proof separates a generic shifted-strength
naturality calculation from the independent fixed projection-tail cancellation;
both are strictly smaller statements and preserve the node's target statement
unchanged.

## New nodes

`lem-sfb-rational-p1-second-projection-interchange-core` records the generic
strength naturality theorem and its proof source. `lem-sfb-rational-p1-second-
projection-interchange-tail` records the fixed projection-tail cancellation.
Both node files and their Lean modules are included in this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SecondProjectionInterchange": "4e32217ceb9ceb3840280046d74161f1ddb8e93e", "Sheaf.Paper.RationalP1SecondProjectionInterchangeCore": "6cd4d37184cf32d416c841f2e7f7481d4837ca0c", "Sheaf.Paper.RationalP1SecondProjectionInterchangeTail": "ec81c76f4331a813773e544e5a3c2242c3ee0995"}, "results": {}, "time": "2026-10-28T05:27:05+0800", "transitive": 0, "version": 1}
```

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
