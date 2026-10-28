## What changed

Added the core scalar naturality statement after fixed pullback-coordinate naturality and proved the assigned theorem by composing `pullCoordinatesIso` naturality with that core statement. The assigned theorem's original `sorry` is closed; the core calculation is split off for parallel proof.

## Proved and sorry left

- Proved: `WeilConjectures.finitePartialTensor_identityNaturality_coordinates_expanded` (1 hole closed).
- Sorry left: `WeilConjectures.finitePartialTensor_identityNaturality_coordinates_expanded_core` (1 hole split off).

## No longer needed

- The theorem node `lem-sf-finite-pullback-tensor-fixed-coordinates` is no longer a proof dependency of this item; the fixed-coordinate definitions remain imported.
- No imports were removed from the source dependency closure.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the complete expanded scalar calculation as one step. The fixed pullback-coordinate naturality is an independent preceding step, so the remaining equation is recorded as a strictly smaller core node.

## New nodes

- `lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded-core`: core tensor-coordinate and upper-star scalar equation, with its proof left for a parallel worker.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpanded": "484981ae76565c1e2f05db549b6df61e845a2810", "Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpandedCore": "88fadbd66554518bc3af0d5860f0be08a07e0db3"}, "results": {}, "time": "2026-10-28T10:01:12+0800", "transitive": 0, "version": 1}
```

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
