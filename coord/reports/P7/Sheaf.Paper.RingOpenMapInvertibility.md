## What changed

Proved `ringOpenMap_isIso` by combining two strictly simpler ingredients: an objectwise normalized refinement isomorphism, the invertible derived open unit, and the existing invertible refinement restriction. The adjunction normalization identifies the canonical `refinementOpenMap` component with the normalized comparison, so it is invertible. Added separate modules and DAG nodes for the normalized comparison and open-unit steps.

## Proved and sorry left

Closed the `ringOpenMap_isIso` hole. Added two split-off `sorry`s: `exists_normalized_refinement_iso` and `openDerivedAdjunction_unit_isIso`.

## No longer needed

The attempted import of `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` was removed because it creates a cycle through `RingOpenRefinement`, which imports this target. The proof uses only the two split-off component statements, `Sheaf.Paper.RefinementOpenRestriction`, and the assembly data.

## Where the brief, the DAG or earlier work was wrong

The running build error named stale imports. The current assembly and restriction imports compile. The full coefficient-construction module cannot be imported here: its left-refinement dependency imports `RingOpenRefinement`, whose target dependency is this module. The coefficient-construction and open-unit arguments therefore have to be represented as lower, separately provable statements in an acyclic route.

## New nodes

- `lem-sf-ring-open-map-normalized-refinement`: `exists_normalized_refinement_iso`, the normalized objectwise comparison used to identify the canonical map.
- `lem-sf-ring-open-map-open-unit`: `openDerivedAdjunction_unit_isIso`, invertibility of the derived open-extension unit.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RingOpenMapInvertibility": "e7a3a19d4808e6732d02a132863b10b32f781582", "Sheaf.Paper.RingOpenMapNormalizedRefinement": "7d27b4e3e9335cd74ca85b15df5b0e8aeab71067", "Sheaf.Paper.RingOpenMapOpenUnit": "e252f4c870a682fc31f483567e2cff38b9799cf5"}, "results": {}, "time": "2026-10-28T01:20:45+0800", "transitive": 0, "version": 1}
```

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
