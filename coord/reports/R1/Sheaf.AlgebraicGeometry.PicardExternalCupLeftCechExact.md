## What changed

Proved `AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_exact` with its
signature and all existing definitions unchanged. Added two modules:
`PicardScalarAffineSectionsExact` gives the scalar section functor and proves its affine
exactness; `PicardExternalAffineRectangleExact` gives the external coefficient functor
and isolates exactness of its sections on a single affine rectangle.

Private proved helpers assemble sectionwise splittings into Cech product splittings,
extend short exact sequences by zero, prove affine finite intersections, and tensor
degreewise vector-space splittings through the actual total-complex summands. Added
proof imports for the two modules and ModuleCat.Projective. Updated the parent DAG
proof to this route. No existing signature, visibility or definition body changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_exact` (1 of 1).
Proved `AlgebraicGeometry.Scheme.Modules.picardScalar_affine_sections_exact`, node
`lem-sc-picard-scalar-affine-sections-exact`, using existing affine Cech acyclicity,
section lifting, sectionwise kernels, and exact scalar restriction.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.picardExternal_affine_rectangle_exact`, node
`lem-sc-picard-external-affine-rectangle-exact`. Its proof is exactly `by sorry`.
This is a decomposition, not a sorry-free proof of the geometric theorem. The remaining
statement concerns one affine rectangle only and contains no Cech, tensor-total,
extension, cover, compactness or diagonal assertion. All categorical assembly is proved.

## No longer needed

No original import was removed: those imports support the existing definitions and
zero-map instances. The original plan's `lem-weil-pbc-qcqs-finite-affine-open-cover`
is not needed: the actual finiteSubcover maps have affine domains directly.
`lem-weil-pbc-quasi-coherent-module-cokernel-image` and its module
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` are not needed: scalar
section exactness instead uses the proved source affine Cech section-lifting result.
No module of either node was newly imported.

The parent no longer directly depends on flat tensor exactness, affine fibre-product
spectra, affine pullback sections, tensor sections, or pullback quasi-coherence.
The pullback adjunction remains a direct dependency through the existing zero-map
instance. Those other geometric dependencies remain needed by the new affine-rectangle node; they
are relocated, not claimed as globally pruned. The tensor-total assembly itself uses
split vector-space sequences and requires no flat-tensor node.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically sound. Its final categorical assembly was not supplied as
a usable declaration; the delivery proves that assembly explicitly. The affine scalar
section step has a shorter route through existing proved Cech acyclicity and lifting.
The Stacks source file is absent on this clone; the specified Tag 0BED was read online.
The unit route is unchanged. There are no forced adaptations or statement changes.
Empty opens and zero coefficients satisfy both new statements; nonempty finite tuples
are essential for affine intersections, since the empty intersection need not be affine.

## New nodes

`lem-sc-picard-scalar-affine-sections-exact` records the proved local scalar-section step
in `Sheaf.AlgebraicGeometry.PicardScalarAffineSectionsExact`.

`lem-sc-picard-external-affine-rectangle-exact` records the one remaining local geometric
step in `Sheaf.AlgebraicGeometry.PicardExternalAffineRectangleExact`. It reduces to the
natural affine pullback/tensor section comparisons and field tensor exactness. There
are no arbitrary witnesses chosen from existence theorems and no new hollow definitions.

## Second reading by R1

1. Compared the complete item module with the repository using diff. Every existing
   declaration signature, visibility, definition body and docstring is unchanged;
   only proof imports, private proved helpers and the target proof were added. The
   two other modules and their declarations are new. No change record is required.
2. Compiled all three modules locally without errors or warnings. A scratch copy
   with `#print axioms` confirms that scalar affine exactness, both new functors and
   their zero-map instances use only propext, Classical.choice and Quot.sound. The
   parent and affine-rectangle theorem additionally use sorryAx, as disclosed.
   The only delivered sorry is the named affine-rectangle theorem, exactly `by sorry`.
   No forbidden declarations or hollow definitions occur. The adjunction chosen in
   zero-map proofs is from a proved theorem and supplies only propositional additivity;
   the degreewise splittings are from proved vector-space projectivity.
3. Read both new statements and their proofs in words against Stacks Tag 0BED
   (https://stacks.math.columbia.edu/tag/0BED), especially its coefficient diagram and
   affine section tensor formula. The rectangle statement is a strictly local part
   of the original argument and is true without compactness or diagonal assumptions.
   Empty opens, zero modules and the one-point affine scheme present no exception:
   rectangle sections are zero in the first two cases, and ordinary vector-space
   tensor exactness gives the third. Repeated cover indices are allowed; tuples have
   length n+1, so the affine-intersection argument never asserts an empty intersection
   is affine. Fresh leanfinder, loogle and grep searches, plus rg on the source tree,
   found no duplicate of the rectangle statement. Existing affine extension lifting
   has the same proved Cech-lifting route already used by the scalar lemma. Closing
   the rectangle would require the natural affine comparison, beyond a short repair.
4. Reviewed the product splittings, extension-by-zero cases and tensor summand
   identities from the parent downward. They prove the actual functor sequences,
   without requiring a splitting as cochain complexes. The original public imports
   support unchanged definitions or signatures. In the new rectangle module removed
   unused TensorSection and Morphisms.Affine imports; imported TensorPullback publicly
   for the definition and its adjunction and Adjunction.Additive privately for proofs.
   The old cover and cokernel-image nodes are unused; affine fibre product, pullback
   sections, tensor sections, pullback quasi-coherence and field tensor exactness move
   to the rectangle node. Affine diagonal intersections and pullback adjunction stay.
   The unit sk-prop-av-cube and its realized route are unchanged; no unit is bypassed.
5. Checked the nodes' verbatim Lean statements, required new-node fields, proof steps,
   proof-origin records and dependency unions. Restored the parent's direct adjunction
   dependency used by its existing zero-map instance. No statement fields were changed.

Second-reading changes: minimized the new rectangle module's imports, corrected the
parent dependency record and pruning explanation, and recorded this review. No holes
were closed or added during the second reading. Overall this delivery closes one old
hole and adds one strictly smaller hole: net zero, a decomposition rather than a
sorry-free proof of the parent.
