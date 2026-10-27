## What changed

The item theorem is proved by reducing an arbitrary `alpha` satisfying `halpha` to the
canonical adjunction transpose. A new module,
`Sheaf.SixFunctors.OpenTensorProjectionMateCanonical`, records the strictly simpler
canonical-mate resolving-pair calculation as the remaining proof step. The canonical
mate is defined directly from the adjunction unit and `restriction.inv`; injectivity of
the exact derived adjunction hom-equivalence proves it equals `alpha`.

The item node proof dependencies were updated to record this route, and the new node
`lem-sf-open-tensor-projection-mate-canonical` was added.

## Proved and sorry left

Proved `WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_resolving`.
One strictly simpler theorem remains with `sorry`:
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical` in node
`lem-sf-open-tensor-projection-mate-canonical`.

## No longer needed

No imports were removed. The previously planned direct preservation and localization
substeps are encapsulated by the canonical-mate node; no additional modules are needed.

## Where the brief, the DAG or earlier work was wrong

The original node proof plan can be reduced first by fixing the mate canonically. The
hypothesis `halpha` then gives equality with that mate by hom-equivalence injectivity.
No statement defect was found.

## New nodes

`lem-sf-open-tensor-projection-mate-canonical` is a strictly simpler resolving-pair
chain equation with the mate fixed by the adjunction transpose. Its declaration is in
`lean/Sheaf/SixFunctors/OpenTensorProjectionMateCanonical.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenTensorProjectionMateCanonical": "99587147ee8d9e53adc35183b8fe4e10c0d7d3af", "Sheaf.SixFunctors.OpenTensorProjectionMateResolving": "f5ea0fe848072fc4138e035b6a73d1af66e4609b"}, "results": {}, "time": "2026-10-28T00:11:13+0800", "transitive": 0, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
