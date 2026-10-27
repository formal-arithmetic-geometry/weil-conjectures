## What changed

The item module now splits on `RingStage`: finite stages call
`exists_normalized_refinement_iso_finite`, and completed integral stages call
`exists_normalized_refinement_iso_integral`. The original theorem is proved by this
case split. Both intermediate modules contain the corresponding named proof step and
are imported privately by the item module. The DAG copy records these two proof
dependencies.

## Proved and sorry left

Proved: `WeilConjectures.ConstructibleExceptionalCoefficients.exists_normalized_refinement_iso`.

Sorry left as the two strict proof-step decompositions:

- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_normalized_refinement_iso_finite`
  (`lem-sf-ring-open-map-normalized-refinement-finite`).
- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_normalized_refinement_iso_integral`
  (`lem-sf-ring-open-map-normalized-refinement-integral`).

The finite and completed integral statements are strictly specialized stages of the
item's RingStage statement and correspond to its two construction steps.

## No longer needed

None. The item still uses the assembly-data and open-restriction declarations through
the two split-off statements.

## Where the brief, the DAG or earlier work was wrong

The direct construction theorem cannot be imported into this item: its import chain
runs through `RingOpenRefinement`, `RingOpenMapInvertibility`, and back to this module.
The original DAG proof described finite and completed integral constructions but did
not expose them as separate declarations, so this delivery records those two missing
proof-step nodes.

## New nodes

`lem-sf-ring-open-map-normalized-refinement-finite` is the finite coefficient
proper/open comparison step; its module is
`lean/Sheaf/Paper/RingOpenMapNormalizedRefinementFinite.lean`.

`lem-sf-ring-open-map-normalized-refinement-integral` is the compatible strict
reduction and normalized total-limit comparison step; its module is
`lean/Sheaf/Paper/RingOpenMapNormalizedRefinementIntegral.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RingOpenMapNormalizedRefinement": "c7489379025a61562714fa29ef3247b7b24e2164", "Sheaf.Paper.RingOpenMapNormalizedRefinementFinite": "bb84e137beea08b4b0dc4fb68aa7f35573890135", "Sheaf.Paper.RingOpenMapNormalizedRefinementIntegral": "f550bde62dc9e835d9c7e42b03779d340d3b8b9e"}, "results": {}, "time": "2026-10-28T03:43:09+0800", "transitive": 0, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
