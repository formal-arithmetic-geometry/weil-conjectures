## What changed

Implemented `finiteSectionSpecialization_scalar_canonical` by constructing the canonical
B-family comparison from the coefficient section maps, scalar pullback comparison, and the
A-family comparison.  The proof establishes normalization using the one-fibre compositor and
then restricts the conjugation identity to the zero fibre, using the scalar section compositor.
The coefficient-map and fibre-square input is recorded in the new
`finiteSectionScalarTransportData` theorem module.

## Proved and sorry left

- Proved `finiteSectionSpecialization_scalar_canonical`.
- Added one strictly smaller split theorem, `finiteSectionScalarTransport_data`, whose proof is
  left as `sorry`; it packages invertibility of the two coefficient section maps and their two
  canonical fibre scalar/base-change squares.

## No longer needed

- Removed the direct imports of `Sheaf.SecSmoothPurity.SectionScalarBaseChange` and
  `Sheaf.SecSmoothPurity.FiniteSectionFamilyConstancy` from the item module.  The item proof uses
  only `ScalarSectionCompositor`; the split data theorem is the sole interface for the remaining
  coefficient-data step.
- The item proof does not use the uniqueness, coordinate-normalization, or specialization-isomorphism
  clauses of the larger `NormalizedTransport` proposition.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan treats the coefficient-map isomorphisms and the one/zero fibre scalar squares
as available ingredients, but no public theorem in the imported closure packages those facts for
arbitrary finite rings.  They are therefore split into the strictly smaller
`finiteSectionScalarTransport_data` statement; the canonical comparison and zero-fibre equation
are proved from that interface.

## New nodes

- `new-lem-sp-finite-section-specialization-scalar-canonical-data`:
  `Sheaf.SecSmoothPurity.FiniteSectionScalarTransportData` /
  `finiteSectionScalarTransport_data`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteSectionSpecializationScalarCanonical": "ec3e5b8b85ece45131a6b4fa4e2b495aa04a4bce", "Sheaf.SecSmoothPurity.FiniteSectionScalarTransportData": "4e36d1b98238f45e52b12288d5c69c75bc18725c"}, "results": {"Sheaf.Paper.FiniteSectionSpecializationScalar": {"hash": "f54d04e74af0c83b9ce4797e47de58e7edc01123", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T03:48:19+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
