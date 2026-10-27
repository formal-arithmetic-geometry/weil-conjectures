## What changed

Restored `lean/Sheaf/Paper/FiniteRingRefinementCoordinates.lean` from the retained
quarantine copy after the returned delivery was dropped from the candidate build.
The existing B7 rework claim was retained.  The companion module
`FiniteRingRefinementCoordinatesCore.lean` isolates the canonical finite
proper/open witness and endpoint coordinate calculation as a strictly simpler
existential statement; the item imports it as the unresolved lower step.
Both modules compile against the current dependency snapshot.

## Proved and sorry left

The original theorem `finite_ring_refinement_coordinates` remains a `sorry`.
The new theorem `finite_ring_refinement_coordinates_canonical` remains a `sorry`;
it is the strictly simpler canonical-witness step required by the parent proof.
No theorem holes were closed; one upper obligation was split into one named lower
statement.

## No longer needed

None.  The two original public imports remain required by the item statement and
the split theorem, and the companion import is required by the split route.

## Where the brief, the DAG or earlier work was wrong

The prior delivery was based on a source that the candidate build removed after
its base commit, so it could not land even though its files compiled.  The
returned repair specifically required restoring the quarantined item source;
this delivery restores that source before reapplying the companion split.  Direct
`rfl` expansion of `finiteImageIso` is not viable under the repository's
irreducibility settings, so the canonical coordinate calculation remains an
intermediate theorem.

## New nodes

`lem-sf-finite-ring-refinement-coordinates-canonical` records the strictly
simpler existential canonical-witness step in
`FiniteRingRefinementCoordinatesCore.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteRingRefinementCoordinates": "832ecbf364446fec480d5ff78ffbfef7427b4d74", "Sheaf.Paper.FiniteRingRefinementCoordinatesCore": "d242c55dbbb2108655615fb131147ff96ba8c533"}, "results": {}, "time": "2026-10-28T02:11:25+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
