## What changed

Proved `AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_restriction`
from naturality of the existing inverse-image composition and single-complex comparisons,
functoriality, and associativity. The fully proved private helper
`trianglePullback_naturality` carries the categorical calculation.

To resolve the previous attempts' 60-second compile failure, factored the existing raw map
through the public generic construction `AlgebraicGeometry.Etale.rawTriangleMap` in the
same module. Unfolding the new helper gives exactly the old composite. Existing signatures,
visibility, imports and mathematical definitions retain their meaning. No downstream
adaptation is required. Change record: `coord/changes/raw-triangle-map-factorization.md`.
The factored diagnostic file compiled in 53.9 seconds; its whitespace warning was removed.
The required `deliver3.py --no-push` dry run printed OK: compilation, axiom probing
and preflight passed, except for the second reading reserved for the next worker.
Nothing was pushed. A separate compiled `rfl` check proves that the refactored definition
equals the verbatim old composite for every parameter; the check is preserved in
`scratchpad/definition-check/lean/Sheaf/AlgebraicGeometry/RawTriangleDefinitionCheck.lean`.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_restriction`
(node `sbc-lem-higher-image-raw-triangle-restriction`). One of one original holes closed.
No holes added, no split-off statements, no sorry remains in the delivered module.
Both the generic data construction and the private helper are complete.
This is a proof, not a decomposition.

## No longer needed

None. Existing imports supply the cohomology presheaf and the inverse-image composition
comparison. The planned dependency `lem-weil-pbc-inverse-image-composition` remains used
through `upperStarComp`. No Sheaf proof dependency is added or bypassed.
The unit `sk-lem-failure-field` has no realized statement or step in this module;
its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or signature error found. The previous proof's compilation was too close
to the hard 60-second limit; repeated validation failed. Sharing the categorical map
construction repairs the implementation cost without changing the mathematical route.
There are no new DAG nodes, unproved dependencies, or forced adaptations.

## Second reading by B3

1. Compared the sole delivered module with the repository using `diff`, and checked
   both existing declaration signatures byte for byte: unchanged. The only definition
   edit is declared in `coord/changes/raw-triangle-map-factorization.md`. Read its users
   and independently compiled the preserved universal `rfl` check against the identical
   sandbox module: the new definition equals the verbatim original composite. No target,
   coefficient data, hypothesis, visibility, or conclusion changes.
2. Independently compiled the delivered module with `lcompile.py`: clean, 51.0 seconds.
   Read the entire categorical calculation; both naturality rewrites have the required
   orientation and functoriality expands restriction as precomposition. No `sorry`,
   forbidden declaration, or arbitrary existence witness occurs. The definition contains
   only the displayed morphism composite. A separate scratch `#print axioms` probe compiled successfully: `rawTriangleMap`,
   the pullback definition and the restriction theorem use exactly `propext`,
   `Classical.choice` and `Quot.sound`; no `sorryAx` is reachable.
3. No statements were split off and no holes were added. The proved private helper is
   strictly generic naturality for the two comparison transformations, with no assumptions
   beyond those used by the original construction. For identity restrictions the equation
   reduces to itself; for zero classes or coefficient maps both sides are zero. No
   invertibility, nonempty object, positive degree, or nonzero coefficient is required.
4. Checked the imported presheaf definition and searched the library and Mathlib for
   triangle/presheaf naturality; independently queried Loogle for
   `CategoryTheory.NatTrans.naturality_assoc`. It supplies the same elementary naturality
   used by this short helper, with no shorter specialized pullback theorem found.
   Existing imports support the presheaf signature and comparison construction; no new
   import was added. The old sole proof dependency remains used through `upperStarComp`,
   so `No longer needed: None` is complete. The unit `sk-lem-failure-field` has empty
   realized statement and step lists, and its route is preserved.
5. Read the node's statement, proof, proof dependencies and proof origin alongside the
   Lean proof. The recorded inverse-image composition/naturality argument is exactly
   the implemented argument; its sole proof dependency remains correct. No new nodes,
   statement changes, or forced adaptations need recording.

Verdict: pass. Second reading changed only this report; the Lean proof, imports, node,
change record and mathematical construction required no repair.
