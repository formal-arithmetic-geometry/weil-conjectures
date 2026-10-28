## What changed

Proved `integral_normalized_ring_refinement_identity_component` in
`lean/Sheaf/Paper/IntegralNormalizedRingRefinementIdentityComponent.lean`.  The proof
extracts the identity normalization witness from `N.refinement_normalized`, applies the
ambient identity-word lemma, and cancels the realization isomorphism.  Added the
self-contained module `lean/Sheaf/Paper/IntegralNormalizedRingRefinementIdentityCore.lean`
for the remaining ambient categorical calculation.

## Proved and sorry left

The item theorem `integral_normalized_ring_refinement_identity_component` is proved.
The new theorem `integral_normalized_ring_refinement_identity_core` remains as one
named `sorry`; it is strictly simpler because it is an ambient coefficient-category
identity and has no coefficient-construction or refinement-comparison data.

## No longer needed

The item proof no longer directly needs the five originally listed proof dependencies:
`lem-sf-integral-normalized-refinement-pasting`,
`lem-sf-integral-compactification-system-realization`,
`lem-sf-integral-refinement-diagram-admissibility`,
`lem-sf-ring-open-refinement`, and
`lem-sf-integral-ringed-clopen-comparison`.  Their required ambient consequence is
isolated in the new core node; the core module imports only the coefficient data and
open-restriction API.

## Where the brief, the DAG or earlier work was wrong

The original proof plan placed all five large system-level dependencies directly under
the component.  The component itself only needs their ambient identity-word consequence,
which is a strictly smaller statement and can be isolated before the coefficient
inclusion cancellation.

## New nodes

`lem-sf-integral-normalized-ring-refinement-identity-core` is added at
`dag/nodes/sec-six-functors/lem-sf-integral-normalized-ring-refinement-identity-core.json`.
It states the ambient proper/open identity word and is the sole remaining proof hole.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralNormalizedRingRefinementIdentityComponent": "b9205bf2f5c273d7f5a9121c4c66642404bb1df7", "Sheaf.Paper.IntegralNormalizedRingRefinementIdentityCore": "5acbc2ed7133492ed97818fca413d9ed16dc7d6a"}, "results": {}, "time": "2026-10-28T08:13:10+0800", "transitive": 0, "version": 1}
```

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
