## What changed

Closed the `canonicalReductionTensorPullComplex_component` proof in the assigned
module.  The item now imports the proof-only module
`Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponentBridge` and applies
its finite-evaluation bridge.  The two bridge hypotheses are discharged by the
existing `tensorReductionStrictMap_component` theorem at `V` and at `U` after
ordinary pullback.  Added the bridge module and its DAG node; no existing
statement or definition was changed.

## Proved and sorry left

The assigned declaration
`WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPullComplex_component`
is proved (one of one item sorries closed).  The new declaration
`WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPullComplex_component_bridge`
in the bridge module remains as one named `sorry`, with its own DAG node.  No
sorry occurs in a definition.

## No longer needed

No existing imports or planned dependency nodes were removed.  The item proof
uses the strict-map finite-component characterization and the new bridge; the
bridge records the ordinary-limit, sequence-pullback, and scalar total-tensor
dependencies required by the finite pure-tensor calculation.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the finite strict-map evaluation rewrite, the
normalized sequence pullback tensor formula, and degreewise assembly into one
component theorem.  The delivery isolates that finite-evaluation bridge as a
strictly smaller intermediate theorem, then combines it with the already proved
strict-map component theorem.  The target statement is unchanged.

## New nodes

Added `lem-sf-canonical-reduction-tensor-pull-complex-component-bridge` in
`dag/nodes/sec-six-functors/lem-sf-canonical-reduction-tensor-pull-complex-component-bridge.json`.
Its Lean declaration is
`WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPullComplex_component_bridge`
in `Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponentBridge`; it
states the degree-n identity under the two finite evaluation characterizations
of the strict reduction maps.  The bridge proof is the pure-tensor and
normalized-unit calculation from the cited Stacks/blueprint step.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponent": "9f57bfb8bae0db65bdfdde519cfc0a3e05f46c7f", "Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponentBridge": "3dafd91f42593dfd15da7712cd69954959a6ec86"}, "results": {}, "time": "2026-10-28T09:32:57+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
