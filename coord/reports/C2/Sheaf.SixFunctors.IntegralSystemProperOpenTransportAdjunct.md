## What changed

Closed `transportedGamma_adjunct` and therefore the existing
`integralSystemProperOpenTransportAdjunct` construction.  The proof cancels the
canonical bridge isomorphism `(b.pull l E i).hom` and reduces the result to the
new bridge-cancellation mate statement.  Added the proof-only import
`Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunctBridge` and its
corresponding split-off theorem.  The module chain compiles in import order.

## Proved and sorry left

The item module has zero remaining sorries.  The following existing declarations
are proved by this delivery:

- `WeilConjectures.IntegralSystemRealization.transportedGamma_adjunct`.
- `WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransportAdjunct`.

Added one strictly simpler split-off theorem, still with `sorry`:

- `WeilConjectures.IntegralSystemRealization.transportedGamma_adjunct_bridge` in
  `Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunctBridge`, node
  `lem-sf-integral-system-proper-open-transport-adjunct-bridge`.

The split-off theorem is the equality after postcomposition with the canonical
pullback bridge isomorphism; the item proof combines it with cancellation.
No definition contains a `sorry`.

## No longer needed

No existing module or node is withdrawn.  The item proof uses only the new
bridge-cancellation theorem and `CategoryTheory.cancel_mono`; no additional
planned proof dependency is imported.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan omitted the explicit bridge-cancellation
identity needed to make the intrinsic semilinear `gamma_adjunct` equation match
the operation-level `properOpenLambda` target.  This delivery records that
identity as a strictly simpler intermediate node.  No target statement or
existing definition was changed.

## New nodes

- `lem-sf-integral-system-proper-open-transport-adjunct-bridge`: the bridge
  cancellation form of adjunct normalization, with the canonical pullback bridge
  isomorphism postcomposed on both sides.  Its Lean declaration is
  `transportedGamma_adjunct_bridge` in
  `Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunctBridge`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct": "abdbfc787c233060769e2299661400dc96bf0f92", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunctBridge": "57971f1dd54e5e439b30e119d7a6de288e79405c"}, "results": {}, "time": "2026-10-28T08:04:52+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
