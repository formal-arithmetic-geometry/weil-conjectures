## What changed

Closed the proof hole in `AlgebraicGeometry.Scheme.finitePerfectAdic_descend_coordinate_transitions` by combining three strictly smaller named components: transition maps with sourcewise universality, actual scalar-realization isomorphisms, and the transition coherence equation. Each component is a public theorem with its own DAG node and is imported privately by the item module.

## Proved and sorry left

Closed 1 of 1 sorries in the item theorem: `AlgebraicGeometry.Scheme.finitePerfectAdic_descend_coordinate_transitions`. Three split-off sorries remain, one in each new theorem: `AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_transition_maps`, `AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_realizations`, and `AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_transition_coherence`.

## No longer needed

None. The original marked-origin and scalar-coherence imports remain needed by the three component statements, and all four proof dependencies remain represented in the component nodes.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was corrected. The original monolithic proof plan could not be completed from the available declarations within this item, so its three independent mathematical components were made explicit as named intermediate theorems. The item proof now follows exactly those component boundaries.

## New nodes

- `new-w5-finite-perfect-adic-coordinate-transition-maps`: `Sheaf.Paper.FinitePerfectAdicCoordinateTransitionMaps`
- `new-w5-finite-perfect-adic-coordinate-realizations`: `Sheaf.Paper.FinitePerfectAdicCoordinateRealizations`
- `new-w5-finite-perfect-adic-coordinate-transition-coherence`: `Sheaf.Paper.FinitePerfectAdicCoordinateTransitionCoherence`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicCoordinateRealizations": "e7fcf39a3272b7a6a2a6009aebd837f51722f18e", "Sheaf.Paper.FinitePerfectAdicCoordinateTransitionCoherence": "f1041a72c17d6c62c06dad54ac52bcb6ca49ff59", "Sheaf.Paper.FinitePerfectAdicCoordinateTransitionMaps": "4514c9e3331c37e29a209988aabd7555c5d44b93", "Sheaf.Paper.FinitePerfectAdicCoordinateTransitions": "d9fa0c59926aca9846475834931b5302e3b5fd15"}, "results": {}, "time": "2026-10-28T08:13:01+0800", "transitive": 0, "version": 1}
```

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
