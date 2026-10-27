## What changed

Added `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose` with one
strictly smaller transpose statement. The item module imports it and proves
`coordinateKunnethFactorization` by injectivity of the derived adjunction hom equivalence.
The parent node's proof and proof dependencies were updated to match this route.

## Proved and sorry left

`coordinateKunnethFactorization` is proved. One strictly smaller theorem remains as a
named split statement: `coordinateKunnethFactorization_transpose` in node
`lem-sfb-etale-coordinate-kunneth-factorization-transpose`; its proof is `sorry` and
records the pullback-counit mate calculation required by the blueprint.

## No longer needed

The item proof directly uses only the new transpose node. The four lower planned nodes
remain the proof dependencies of that split statement, so none is pruned from the
argument's dependency closure.

## Where the brief, the DAG or earlier work was wrong

The original item proof plan bundled the entire mate calculation with the final
adjunction cancellation. The Lean interface makes the cancellation short, so the mate
calculation was split off as a separate, strictly smaller theorem rather than being
repeated in the item proof.

## New nodes

`lem-sfb-etale-coordinate-kunneth-factorization-transpose` states the equality after
pullback and composition with the counit. It is strictly simpler than the item equality
because it is the image under the adjunction transpose and does not conclude equality in
the right-adjoint target. Its source is the first-triangle coordinate interchange
calculation in the latest blueprint.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorization": "ee49a4731613a4d56b66bdf312553e8e11248490", "Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose": "ac67bc11d998b1ccb1a9ab09c0a28ecdbe240a40"}, "results": {}, "time": "2026-10-27T23:29:20+0800", "transitive": 0, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
