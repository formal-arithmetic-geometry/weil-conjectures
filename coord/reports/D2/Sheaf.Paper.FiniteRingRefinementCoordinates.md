## What changed

Completed `finite_ring_refinement_coordinates` without changing its signature. The proof uses the existing `FiniteRingRefinementCoordinatesCore` witness and adds the private proof import `Sheaf.Paper.RingOpenMapOpenUnit`. A proved private categorical helper `normalized_iso_unique` establishes uniqueness from the two open-unit normalization equations: the transpose and unit are invertible, hence the common restriction factor is invertible and cancels. Substitution gives the coordinate formula. The item's node now records these actual dependencies. `lcompile.py` compiled the final file cleanly in 3.3 seconds, including the current unpublished canonical companion in its private overlay.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.ConstructibleExceptionalCoefficients.finite_ring_refinement_coordinates` (node `lem-sf-finite-ring-refinement-coordinates`). Also proved the private helper `normalized_iso_unique`. The item contains zero remaining holes. Added zero holes and zero split-off statements. The proof uses the previously existing `WeilConjectures.ConstructibleExceptionalCoefficients.finite_ring_refinement_coordinates_canonical` (node `lem-sf-finite-ring-refinement-coordinates-canonical`) in the unchanged companion module; its existing sorry is not closed here.

## No longer needed

No imports or modules are removed. The node no longer needs direct proof edges to `def-pur-integral-compact-support-coefficient-data`, `def-weil-frobenius-witnessed-compactification`, `lem-pur-compact-support-integral-coefficient-comparison`, `lem-weil-derived-direct-image-composition`, or `lem-weil-pbc-proper-open-comparison-proetale`: the geometry and coordinate formula are supplied by the existing canonical-witness node. These dependencies remain needed transitively or by the statement and are not withdrawn or claimed globally pruned. Both original public imports remain necessary for the statement. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The shared snapshot lagged the current server: the server already imports the canonical companion but retains the parent's sorry. Work used the current server source and node. The queue currently assigns proof work, not the historical bad-import build error. No further split is needed: the existing canonical witness plus the proved open-unit theorem suffice. The uniqueness argument does not assume a cartesian refinement square, nonempty opens, nonzero objects, or any extra boundedness hypothesis.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteRingRefinementCoordinates": "bfd2cca5df6e56576d8d9a091b9207ca491852e3"}, "results": {"Sheaf.Paper.NormalizedRingRefinementLaws": {"hash": "9172ca73948f5e8f4ac9ba533505e36e74c78232", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T05:01:27+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
