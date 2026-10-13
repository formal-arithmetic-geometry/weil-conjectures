## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.OpenRestrictedOrdinaryComparisonSquare`
by a complete Lean assembly from the existing
`ModuleCat.exists_baseDerivedTensor_ringIso_square` and the new geometric theorem
`exists_openRestricted_tensor_coordinate_data`. The latter has its own module and
node and states only compatible stalk ring/chain coordinates and the ordinary
homology target equation: no localizedComparison, no base-derived tensor source,
and no existential source isomorphism of the comparison square.

The proof instantiates the existing universal tensor counit square, postcomposes
it with the geometric target factors, cancels two isomorphism pairs, and identifies
the composites with comparisonIntoTensorPullback using Functor.map_comp.
All original signatures, universes, public imports and definitions are unchanged.
The two new imports in the item are proof-only imports.

## Proved and sorry left

Closed: `AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_ordinary_comparison_square`
(node `lem-pc-open-restricted-ordinary-comparison-square`); no sorry remains in the item.

Added: `AlgebraicGeometry.SingleComplexBaseChange.exists_openRestricted_tensor_coordinate_data`
(node `lem-pc-open-restricted-tensor-coordinate-data`), exactly one named theorem
with `:= by sorry`, a source and a full proof in words. This delivery is a
decomposition: one upper hole closed, one strictly lower geometric hole added.
The universal base-derived source transport is discharged by an existing theorem.
No assertion that the full import closure is sorry-free is made.

Local compilation of the complete two-module set passes with no warnings.
The empty-open case has no point; top opens, zero complexes and zero rings follow
the same scalar, tensor and exact-homology identities. The new statement requires
neither K-flatness nor invertibility of the horizontal comparison.

## No longer needed

No original library import or original proof dependency is globally pruned.
The original geometric dependencies now belong to the new geometric node; the
ring-isomorphism naturality node is used directly by the item's Lean proof.
Both original public imports are needed by the item's unchanged statement.
The new geometric module needs only OpenRestrictedTensorComplexIso: the tentative
AffineSpectrumOrdinaryComparisonSquare import there was removed after compilation.

Discarded the earlier sandbox-only OpenRestrictedOrdinaryComparisonSquareCore
module: it merely restated the target and is not delivered or imported.
Removed the earlier sandbox copy of OpenRestrictedTensorComplexIso: this delivery
makes no changes to that library module. No unrelated adaptation is delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt moved the entire statement into a renamed core theorem,
which is not a reduction. Lack of a ready-made open geometric transport equation
is resolved here by stating that geometric argument part, while actually using
the existing generic ring-isomorphism theorem for the source comparison.

It would be false to demand the target transport equation for every arbitrary
compatible q and t: their normalization must be the same-germ geometric one.
Therefore the new theorem jointly asserts existence of coordinates and their
target equation. The proof outline constructs these normalized maps directly.
No data is defined by selecting arbitrary witnesses from an unproved existence.
The unit record has empty realized statement and step lists; no unit route is bypassed.

## New nodes

`lem-pc-open-restricted-tensor-coordinate-data`, in
`dag/nodes/sec-picard-framework/lem-pc-open-restricted-tensor-coordinate-data.json`:
the geometric ring/chain coordinates and ordinary tensor target transport of
steps 1 and 3 of the original plan. Its module is
`Sheaf.AlgebraicGeometry.OpenRestrictedTensorCoordinateData`.
The parent node's proof, proof_deps and proof_origin now match the Lean assembly.
No change record is required because no existing statement or definition changes.

## Second reading by B4

1. Compared both delivered modules with the repository versions. Existing theorem signatures and all definitions are unchanged byte for byte; the only interface additions are the explicitly documented proof-only imports and the new split theorem.

2. Compiled the complete sandbox module set with `lcompile.py --all`; both modules compile without errors or warnings. The target theorem has no `sorry`; the only remaining hole is the named `exists_openRestricted_tensor_coordinate_data`, with its node and docstring. No forbidden declarations or hollow definitions were introduced.

3. Checked the split statement against its node and downstream use. It is a strictly lower coordinate-transport statement, does not restate the target, and supplies exactly the data consumed by the target proof. Its edge cases and type parameters are consistent with the target's arbitrary open, point, degree, and complex. The node records the same statement, dependencies, source, and proof route.

4. Checked the proof route and pruning. The target proof uses the existing base-derived tensor ring-isomorphism theorem and the new geometric coordinate theorem, then only categorical composition/cancellation. The original public imports remain needed for the statement; the new imports are proof-only. The discarded core restatement and unused tentative import are not delivered. No unit-level theorem or definition was changed.

5. Checked DAG consistency. The parent node's proof and proof dependencies match the Lean proof, and the new node records its Lean declaration and source. The unit's `realized` lists are empty in the repository unit record, so there was no realized unit step to bypass; the report preserves the unit association and flags this existing blueprint metadata gap.

Changed during second reading: no Lean code or DAG changes; added this review section and verified the dry-run delivery checks.
