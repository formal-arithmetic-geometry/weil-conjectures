## What changed

Proved `AlgebraicGeometry.closed_point_affine_dimension_data` with its exact existing
signature. The proof chooses an actual affine neighbourhood, uses Mathlib's
fraction-field and canonical restriction maps, reuses the proved finite-residue-field
theorem in `WeilConjectures.PointCount`, and transports the existing finite-type-domain
dimension theorem along the canonical fraction-field algebra equivalence. The structural
algebra maps are checked by germ restriction and residue-map functoriality.

Added a private proof import of `WeilConjectures.PointCount`; removed unused imports
listed below. Updated the node's six steps and proof dependency union to match the
implementation. Change record: `coord/changes/closed-point-affine-dimension-proof-imports.md`.

Searches: msearch LeanFinder for the closed-point affine chart data returned component
facts only; Loogle for `"functionField", "IsAffineOpen"` returned the exact fraction-field
ingredient; msearch grep found `primeIdealOf_isMaximal_of_isClosed`. Direct rg found
PointCount's already proved finiteness and composition theorems and the dimension theorem.
No new result is stated. The unit's realized lists are empty for this auxiliary node;
its required chart/dimension argument and all six mathematical conclusions are retained.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.closed_point_affine_dimension_data`
(node `lem-trf-closed-point-affine-dimension-data`).
Added 0 holes. Split off 0 statements. No `sorry` remains in the delivered module.
The dimension theorem is used as an existing declaration, as required by the stage.

## No longer needed

Removed `public import WeilConjectures.Topology.PresheafModuleStalkFunctor`: no
presheaf module functor is used; Mathlib already provides all ring stalks in the statement.
Removed `import Mathlib.RingTheory.Jacobson.Ring`: PointCount already proves the required
finite-residue-field assertion, so no direct Jacobson ring proof is needed here.
No source-library declarations or modules are withdrawn.

Removed from direct proof dependencies `def-weil-pbc-module-stalk`,
`def-weil-pbc-localization-at-prime` and `def-weil-pbc-finite-type-algebra`:
their notions remain in statement dependencies, while fraction-field, restriction and
dimension APIs handle the proof. No standalone proof of the local residue field
identification with A/m is needed; PointCount supplies the finiteness conclusion.
All remaining declared dependencies are retained. No entire DAG node can be claimed
unreachable from the targets on this basis.

## Where the brief, the DAG or earlier work was wrong

No statement error found. Step 5's proposed reconstruction of the residue field was
unnecessary: PointCount already proves finiteness for the exact structural map, with
only locally finite type and closedness, including non-quasi-compact schemes.
Step 6's recorded theorem is stated for FractionRing A, so the implementation explicitly
restricts its canonical equivalence to K and transports transcendence degree.
No statement or definition repair, forced adaptation, or new node was needed.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
