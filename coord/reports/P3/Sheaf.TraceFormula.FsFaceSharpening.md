## What changed

Completed `AlgebraicGeometry.face_sharpening` in
`Sheaf.TraceFormula.FsFaceSharpening`, preserving its complete statement.
The proof uses `faceLocalization_fineSaturated` and proved private helpers to:
identify the localization units, prove fs of Associates, construct the canonical
quotient embedding and its group-completion equivalence, and prove torsion-freeness
from sharpness and saturation. Mathlib supplies finite generation of group
completions and `Module.basisOfFiniteTypeTorsionFree'` supplies the finite basis.

Updated `lem-trf-fs-face-sharpening` to record this argument. Removed the public
imports of the two unused Sheaf dependency modules, replaced them with the public
Mathlib quotient/saturation interfaces actually needed, and added the private
finite-localization import. All new helpers are private and proved. The import
change is recorded in `coord/changes/fs-face-sharpening-imports.md`.

Validation: the item compiled cleanly in 9.5 seconds, and again in 13.5 seconds
in the verification batch. All 36 unchanged direct importers compiled against the
new item, each within 15 seconds; no consumer adaptation was needed. A temporary
importing module checked `#print axioms AlgebraicGeometry.face_sharpening`, which
reported exactly `[propext, Classical.choice, Quot.sound]`. All 36 unchanged
consumer copies and the temporary axiom-check module were removed before delivery.
The theorem signature was compared verbatim with the original and is unchanged;
all Lean lines are at most 100 columns. Edge cases in the proof require no extra
assumptions: F = Q, F containing only units, a trivial monoid, an empty generating
set, and monoids with torsion units are permitted. In particular the proof never
asserts that Q^gp itself is torsion-free.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.face_sharpening`
(node `lem-trf-fs-face-sharpening`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining: 0.
There are no remaining sorry declarations in the item and none are added elsewhere.
This is a proof, not a decomposition. No existing theorem or definition statement
was changed, and no data is chosen from an unproved existence statement.

## No longer needed

- `Sheaf.AlgebraicGeometry.FaceLocalizationUnits`, node
  `lem-trf-face-localization-units`: the multiplicative submonoid realization admits
  a direct units proof by clearing denominators and applying the face condition.
  Removed its import and proof dependency; its existing declaration stays intact.
- `Sheaf.AlgebraicGeometry.FaceSubgroupSaturated`, node
  `lem-trf-face-subgroup-saturated`: a sharp saturated monoid has torsion-free group
  completion directly, so the separate face-subgroup saturation result is unused.
  Removed its import and proof dependency; its existing declaration stays intact.

Both modules had this item as their only direct Lean importer in the shared
snapshot. No module or DAG node is deleted. The external proof dependencies that
remain are `lem-trf-face-localization-fs` and the Mathlib leaf
`lem-trf-fg-torsionfree-group-free`. The source unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The two existing face-unit/subgroup declarations
use additive localization presentations, whereas the item uses multiplicative
submonoids inside the Grothendieck group. Direct proofs avoid those representation
transports. The former DAG route is mathematically valid but the face-subgroup
saturation input is unnecessary: saturation puts a torsion group element and its
inverse in the sharp monoid, where they must be trivial.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
