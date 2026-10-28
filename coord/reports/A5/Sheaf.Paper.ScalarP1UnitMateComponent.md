## What changed

Closed `AlgebraicGeometry.ProEtale.RationalP1.scalar_p1_unit_mate_component` by
applying the categorical assembly theorem `scalar_component_from_trace` to the
explicit witness supplied by `scalar_trace_equation`. The assigned module is
now a small compiling wrapper; its former private calculation scaffold was
removed because it was unused by this route.

The interface change is recorded in `coord/changes/scalar-p1-unit-mate.md`.

Added six strictly smaller split statements: the unshifted Tate-line
composition, ambient square assembly, ambient twisted-unit mate, the shifted
line square, the packaged scalar trace witness, and the component assembly
from that witness. These are the remaining proof obligations for the route.

## Proved and sorry left

Closed one assigned hole:
`AlgebraicGeometry.ProEtale.RationalP1.scalar_p1_unit_mate_component`.

Six split holes remain, each in its own declaration:

- `lineComparison_comp`
- `ambient_square_assembly`
- `ambient_twisted_unit_mate`
- `shifted_line_square`
- `scalar_trace_equation`
- `scalar_component_from_trace`

No definition or instance contains a `sorry`.

## No longer needed

The former private helper scaffold in the assigned module is no longer needed;
it was removed rather than imported by the final wrapper. The intermediate
`SecondTraceExchangeEquation` split was superseded by the packaged
`ScalarTraceWitness` and was withdrawn before delivery. No existing public
module was changed, and the public imports needed by the target remain.

## Where the brief, the DAG or earlier work was wrong

The original one-step route mixed the large categorical target with the costly
trace equality conversion. Packaging that equality as `ScalarTraceWitness`
keeps the intermediate statement strictly smaller and makes the target compile
within the per-file limit. The target statement itself is unchanged.

## New nodes

- `lem-sfb-rational-tate-line-comparison-composition`
- `lem-sfb-ambient-square-assembly`
- `lem-sfb-ambient-twisted-unit-mate`
- `lem-sfb-shifted-line-square`
- `lem-sfb-scalar-trace-equation`
- `lem-sfb-scalar-component-from-trace`
- `lem-sfb-derived-calculation-instances`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AmbientSquareAssembly": "da2487c26fa8dbfee5dbbeec6be7741b93de5263", "Sheaf.Paper.AmbientTwistedUnitMate": "fb607f71b218fa2328cdc12b2ef620c85e430e86", "Sheaf.Paper.DerivedCalculationInstances": "ad4968a83455ec04e62721fce740ede86ae51b1e", "Sheaf.Paper.RationalTateLineComposition": "9d0ac344baca5ff637401ef4a6c313d70667adce", "Sheaf.Paper.ScalarComponentFromTrace": "2f717160f5d3cd72ff942a9789a9a1682ead6618", "Sheaf.Paper.ScalarP1UnitMateComponent": "532c89db1d2eb27a104d3e7c6cbf9d173fdcbc7d", "Sheaf.Paper.ScalarTraceEquation": "e63e2ca4c413637389ed98e06ba4aefbb6ce5516", "Sheaf.Paper.ShiftedLineSquare": "9508681127a078b0ebd580718d97df56723a02d1"}, "results": {"Sheaf.Paper.RationalP1ScalarChernBaseChangeUnit": {"hash": "08f873cd81d0f4854a29e0778513a4bcf04f613b", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T09:46:40+0800", "transitive": 0, "version": 1}
```

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
