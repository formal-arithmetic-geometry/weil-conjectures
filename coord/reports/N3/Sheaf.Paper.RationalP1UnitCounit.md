## What changed

Restored the proven M1 route in `Sheaf.Paper.RationalP1UnitCounit` for the assigned
quarantined build repair. The module now imports the localizing-preservation package,
the normalized restriction package, the unbounded base-change extension, the admissible
generator exchange theorem, and the localizing projection package. It proves
`AlgebraicGeometry.ProEtale.RationalP1.localizingPreservation` by projecting the
existing preservation checks and proves `unitInversions` using the existing canonical
exchange extension and native projection mate. The public statements and definitions
are unchanged. The existing `counitInversion` proof and `unitCounit_exact` hole are
retained.

The two existing DAG nodes were updated so their proof steps, dependencies, and proof
origin match the restored Lean route.

## Proved and sorry left

Closed two of the three holes present in the restored module:

- `AlgebraicGeometry.ProEtale.RationalP1.localizingPreservation`.
- `AlgebraicGeometry.ProEtale.RationalP1.unitInversions`.

No new holes were added. One existing hole remains:

- `AlgebraicGeometry.ProEtale.RationalP1.unitCounit_exact`, with node
  `det-prop-p1-adjunction-rational-unit-counit`.

## No longer needed

The duplicated private naturality and normalized-restriction proof code and the direct
proof imports `Sheaf.Paper.RationalP1TensorShiftNaturality` and
`Sheaf.Paper.RationalP1ProjectionNaturality` are removed. Their functionality is
provided by the imported normalized restriction module. The old direct inversion route
through the general bounded constructibility and field projection statements is replaced
by the existing admissible-generator exchange and native localizing projection
interfaces. No module is withdrawn and no new node is needed.

## Where the brief, the DAG or earlier work was wrong

The global build error was caused by the quarantined dependency closure and reported
many direct imports as bad imports. The restored source itself compiled, but retained
the pre-repair implementation. The M1 proof route is a compatible repair: it uses the
existing localizing-preservation and normalized-restriction declarations and avoids the
stale direct import chain. The exactness hole remains a separate obligation because
normalized component naturality does not establish shift compatibility of the specified
pastes.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.RationalP1UnitCounit": "70aaae1b8af1c46a532c35488aeb106cd872de43"}, "results": {"Sheaf.Paper.AffineLineAdjunctionAssembly": {"hash": "b184d314427bd2c03760347cc2996cebd55315cd", "status": "OK"}, "Sheaf.Paper.RationalP1KernelContractions": {"hash": "f7b75505a18f395645cc716a7d590b6c67ce8e2a", "status": "OK"}, "Sheaf.Paper.RationalP1Triangle": {"hash": "d1e2d798a7453c8ae09756e0efc410fa7b065150", "status": "OK"}}, "seconds": 83, "time": "2026-10-28T03:03:34+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
