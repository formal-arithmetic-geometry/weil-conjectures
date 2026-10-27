## What changed

Filled `integral_normalized_ring_refinement_identity` by reducing its natural-isomorphism
identity to the pointwise identity after the faithful integral coefficient inclusion. Added
`Sheaf.Paper.IntegralNormalizedRingRefinementIdentityComponent` for that strictly weaker
pointwise calculation and imported it privately for the proof.

## Proved and sorry left

The assigned theorem `integral_normalized_ring_refinement_identity` is proved with no
`sorry`. The delivery adds one named split-off theorem, intentionally left as `sorry`:
`integral_normalized_ring_refinement_identity_component` in node
`lem-sf-integral-normalized-ring-refinement-identity-component`. No definition contains a
`sorry`.

## No longer needed

No proof-dependency imports were removed from the new component's planned argument. The
item itself uses only the component theorem and its construction-data import; the five
geometric declarations are retained as dependencies of the split component node.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan described the full identity calculation but had no Lean
statement isolating its pointwise faithful-image step. The delivered component node records
that strictly weaker step, allowing the target isomorphism equality to be proved by
`Iso.ext`, natural-transformation extensionality, and faithfulness.

## New nodes

`lem-sf-integral-normalized-ring-refinement-identity-component` records the pointwise
faithful-component calculation and is stated in
`lean/Sheaf/Paper/IntegralNormalizedRingRefinementIdentityComponent.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralNormalizedRingRefinementIdentity": "d9f12d4264ab65b0cb756de523da2f11cff5158a", "Sheaf.Paper.IntegralNormalizedRingRefinementIdentityComponent": "0508dd14d7382d1500fa0beaae8c914e717b85b5"}, "results": {}, "time": "2026-10-28T05:20:27+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
