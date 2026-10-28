## What changed

Restored the complete F1 proof of `AlgebraicGeometry.ProEtale.FiniteProjectionExchange.open_factor_assembly` in `Sheaf.Paper.FiniteProjectionOpenAssembly`. Added the private imports and proved helper module `Sheaf.Paper.FiniteProjectionOpenRestrictions`, which establishes the canonical open route equalities used by the assembly. Updated the item's proof plan and dependencies to match the implemented route.

## Proved and sorry left

Closed the one original `sorry`, `AlgebraicGeometry.ProEtale.FiniteProjectionExchange.open_factor_assembly` (node `lem-sf-finite-projection-open-assembly`). The added `open_factor_routes` theorem (node `lem-sf-finite-projection-open-routes`) is also fully proved. No `sorry` remains and no new `sorry` was added.

## No longer needed

The assembly module no longer imports or uses `lem-sf-open-tensor-normalization` or `def-exchange-projection`; the open route calculation is supplied by `open_factor_routes`, and the remaining assembly uses the fixed coordinate definitions. `lem-sf-finite-projection-tensor-square` remains transitively needed by the new open-restrictions helper. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier landing already contained a complete proof, but it was removed during the red-build quarantine/rework cycle and the module was restored to its original `sorry`. The current build error was a stale bad-import artifact; the restored dependency modules compile, and the prior proof compiles against the current source snapshot.

## New nodes

Added `lem-sf-finite-projection-open-routes`, realized by `AlgebraicGeometry.ProEtale.FiniteProjectionExchange.open_factor_routes` in `Sheaf.Paper.FiniteProjectionOpenRestrictions`. It records the proved equality of the two open routes and both restriction-to-`openSource` identities used by the assembly proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteProjectionOpenAssembly": "913d6d6fb54946b63d9a97c09cc89146e429a235", "Sheaf.Paper.FiniteProjectionOpenRestrictions": "4101f264bdb39e6dbdff2f94ef811b9946cbbee0"}, "results": {"Sheaf.Paper.FiniteProjectionExchangeTransposes": {"hash": "d8b03375179e6eef5b2f6222a08492d2b31333f7", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T09:44:52+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
