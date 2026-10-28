## What changed
Added `TwoTermFreeHomTensorCoordinateMap`, moving `IsSignedHomTensor` and splitting the
finite-free proof into coordinate existence and coordinate uniqueness theorems. The item
combines those two statements to prove `twoTermFreeHomTensor_component_isIso`.

## Proved and sorry left
The item theorem `twoTermFreeHomTensor_component_isIso` is proved from the two split
coordinate statements. Sorry remains in `twoTermFreeHomTensor_coordinate_exists` and
`twoTermFreeHomTensor_coordinate_unique` in the new module; these are the finite-free
construction and its Hom-product uniqueness step, respectively.

## No longer needed
The direct in-file tensor decomposition attempt was removed. No declared proof dependency
was pruned; the three source definitions remain needed by the split statements.

## Where the brief, the DAG or earlier work was wrong
The original plan treated a large sheaf-level finite-free calculation as a single theorem;
Lean elaboration exceeds the file limit when all totalization and Hom-product constructions
are unfolded together. The split statements are strictly lower: existence of the signed
coordinate map and uniqueness of a map satisfying its coordinate formula.

## New nodes
`lem-sf-two-term-free-hom-tensor-coordinate-existence` records the finite-free coordinate
construction. `lem-sf-two-term-free-hom-tensor-coordinate-uniqueness` records the product
projection uniqueness argument.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents": "22fd0dad2b2b496a9244bac3c6b8126cf794caa5", "Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap": "da90f6ff77e210f33891a74f271335177a23ebbf"}, "results": {"Sheaf.Paper.IntegralHomComparisonRepresentative": {"hash": "2e6173be1f203203891b0648b96a370b88230b74", "status": "OK"}}, "seconds": 37, "time": "2026-10-28T08:12:59+0800", "transitive": 0, "version": 1}
```

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
