## What changed

Replaced the sorry in `ModuleCat.exists_baseDerivedTensorCohomologyModel_triangle_rows`
with a complete Lean reduction through the ordinary tensor-algebra triangle row.
Its signature, visibility and existing docstring are unchanged.

Added `Sheaf.Algebra.Homology.BaseDerivedTensorOrdinaryTriangleRows`, which isolates the
row before extension to C. This is strictly the first part of the argument: it has no
flatness assumption and uses ordinary `comparison`, not `localizedComparison`; its maps
are over A tensor_R B, not C. The original theorem performs the final extension itself.

Added and proved `Sheaf.Algebra.Homology.ScalarCoefficientTriangleBoundary`.
Its theorem has no derived category, model, distinguishedness or flatness assumptions.
The proof computes the third-map square on tensor generators, uses naturality of the
homology shift, and proves exact-restriction compatibility from short-complex homology.

In the item's module, proved four private helpers: `extend_exact_row`,
`transpose_square`, `coefficient_naturality`, and `localized_arrow_square`.
The completed proof extends the ordinary arrows, preserves all three exact short
complexes by flatness, and transposes all four ordinary squares using `localized_eq`.
The three arrow squares use coefficient naturality and exact-restriction homology
naturality; the fourth uses the newly proved coefficient-boundary theorem.

Added two proof-only imports for the new modules and one proof-only Mathlib import
`Mathlib.Algebra.Category.ModuleCat.Descent` for flat extension exactness.
All existing public imports remain necessary for the unchanged statement.
Updated the item's DAG proof, proof_deps and proof_origin to match the implemented route.
No definition, existing signature, target, other group's module or unit route was changed.

## Proved and sorry left

Closed the one original hole, by declaration:
`ModuleCat.exists_baseDerivedTensorCohomologyModel_triangle_rows`
(node `lem-pc-base-derived-tensor-cohomology-triangle-rows`).
This is a decomposition, not a proof independent of sorry: one ordinary derived-row
hole is added, so the delivery's net textual hole count is zero.

Proved with no sorry dependencies beyond standard axioms:
`ModuleCat.scalarCoefficient_triangle_boundary`
(node `lem-pc-scalar-coefficient-triangle-boundary`), including its two private helpers.
The item's four private helpers are also proved entirely from Mathlib and model data.

The only sorry left anywhere in this delivery is
`ModuleCat.exists_baseDerivedTensorCohomologyModel_ordinary_triangle_rows`
(node `lem-pc-base-derived-tensor-ordinary-triangle-rows`).
Its whole proof is `:= by sorry`, with source and the complete natural-language
construction in its docstring and node. No sorry occurs in any definition or
inside the proof of the original theorem.

All three delivered modules compile with `lcompile.py --all` within the per-file
60-second limit, without warnings. The delivery dry run checks the axioms again.

## No longer needed

No existing import was removed: the existing three public imports are statement imports.
No unused proof imports remain.

The previous direct dependencies
`lem-pc-base-derived-tensor-cohomology-model-localized-independence`
(`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence`) and
`lem-pc-base-derived-tensor-cohomology-model-map`
(`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelMap`) are not used by this route.
They were not already imported by the item, and are not added.
The ordinary-row construction uses universal functor uniqueness directly; it does not
need the specialized localized independence theorem or the specialized model-map theorem.

`lem-pc-base-derived-extension-resolution`
(`Sheaf.Algebra.Homology.BaseDerivedExtensionResolution`) is no longer a direct
proof dependency of the item; it remains needed by the new ordinary-row node,
and is therefore not claimed as globally pruned.

No blueprint unit statement or realized step is bypassed; the unit's realized lists
are empty and the same distinguished-triangle derived-tensor route is retained.

## Where the brief, the DAG or earlier work was wrong

The planned resolution theorem provides a triangulated derived functor and invertible
counits on resolutions, but its signature does not provide counit shift compatibility.
Thus neither it nor the model-map theorem directly closes the ordinary boundary square.
The remaining ordinary-row node explicitly records this K-flat-resolution augmentation
and universal-transport step instead of treating it as an already available API lemma.

The old plan combined two different steps: producing the universal derived row and
transporting an ordinary row to C. The latter requires no derived-model uniqueness
once the ordinary row is given; it is now proved explicitly by flatness and adjunction.

LeanSearch returned Internal Server Error; this is recorded as unavailable and no
mathematical verdict is inferred from that failure. Loogle, LeanFinder and local
Mathlib/source-library searches supplied the usable generic ingredients.

Edge cases checked in the mathematical statement analysis: C may be zero, in which
case flat extension gives the zero exact row; the unlocalized lemma imposes no condition
on C. Zero input triangles and arbitrary integer degrees require no additional binder.
The coefficient-boundary proof uses only tensor generators and naturality, so zero rings,
zero maps, and non-distinguished/unbounded triangles are covered by its actual Lean proof.

## New nodes

`lem-pc-base-derived-tensor-ordinary-triangle-rows`:
`Sheaf.Algebra.Homology.BaseDerivedTensorOrdinaryTriangleRows`, declaration
`ModuleCat.exists_baseDerivedTensorCohomologyModel_ordinary_triangle_rows`.
This is the unlocalized universal derived-row part of the parent plan; it retains the
one unresolved construction, with all tensor-algebra actions and ordinary counit squares.

`lem-pc-scalar-coefficient-triangle-boundary`:
`Sheaf.Algebra.Homology.ScalarCoefficientTriangleBoundary`, declaration
`ModuleCat.scalarCoefficient_triangle_boundary`. This generic coefficient-boundary
transport statement is fully proved; its only non-Mathlib proof dependency is the already proved scalar-extension
additive instance in the model module; no model data are used. Its source, searches and degreewise argument are recorded.

No change record is needed: no existing statement, definition or public import changed.

## Second reading by C3

1. Compared the delivered parent module against the repository version. Existing declarations keep the same signatures and visibility; only the proof and proof-only imports changed. Verdict: unchanged interface.
2. Compiled all three delivered modules with `lcompile.py`; there are no compiler errors or warnings. The parent hole is closed, and the ordinary-row theorem is the sole explicitly split-off `sorry`, with a matching docstring and DAG node. Verdict: proof checks pass with the documented decomposition.
3. Read both new statements and checked edge cases including zero rings, zero maps, arbitrary degrees, and absence of flatness assumptions in the ordinary and coefficient lemmas. The coefficient-boundary statement is strictly generic and its hypotheses match its proof. Verdict: statements are true and appropriately strong; no duplicate declaration was found locally.
4. Checked the proof route against the unit record and DAG dependencies. The parent uses the ordinary-row node and the coefficient-boundary node, while flat extension exactness is handled directly by Mathlib. Removed no existing imports and identified no additional pruning. Verdict: route and dependency metadata agree with the Lean proof.
5. Checked `proof`, `proof_deps`, `proof_origin`, new-node metadata, and the report against the implemented declarations. Verdict: metadata is consistent.

Changed during second reading: appended this review section only; no Lean code or DAG metadata required repair.
