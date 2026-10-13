## What changed

Replaced the sorry in `AlgebraicGeometry.singleComplexOpenComparison_affine_union`
with a complete proof from a new diagram-construction theorem. The existing signature,
visibility, public imports and docstring are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnionTriangles` and updated the parent node's
proof, proof dependencies and proof origin.

The proof derives quasi-separatedness of X, compactness of the affine V, and compactness
of the overlap. It then obtains the comparison triangles, proves that the biproduct of
the U and V comparison maps is invertible using `biprod.mapIso`, transports the local
hypotheses to the triangle components, and applies
`Pretriangulated.isIso₁_of_isIso₂₃`. The last rewrite identifies the first component with
the exact comparison in the unchanged conclusion.

The new theorem constructs triangles and their comparison morphism, with all three
component equations. It has no local-isomorphism hypotheses and no isomorphism conclusion.
It generalizes the geometric part to two compact opens with compact overlap. No scheme,
coefficient, functor or morphism definition was added or changed; existential triangle
witnesses are eliminated only inside a theorem proof.

Both modules compile locally without warnings (about four seconds each). The edge cases
of the new statement were checked mathematically: empty opens and zero coefficients give
zero terms, repeated opens give the split restriction sequence, and contained opens use
the same sequence. There is no implicit assumption that U union V covers X.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.singleComplexOpenComparison_affine_union`
(node `lem-pc-single-complex-open-affine-union`). No sorry remains in the item's module.

Added exactly one hole:
`AlgebraicGeometry.singleComplexOpenComparison_union_triangles`
(node `lem-pc-single-complex-open-union-triangles`, module
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnionTriangles`). Its proof is exactly
`:= by sorry`, with the source and complete construction argument in its docstring.

This is a decomposition, not an unconditional proof of the target closure: one upper
hole closed and one lower hole added, net zero. The new hole is the geometric/naturality
diagram construction only. Compactness of the overlap, biproduct invertibility and the
actual two-out-of-three inference are proved in the original module. The lower theorem
cannot simply be applied to return the original IsIso conclusion.

## No longer needed

No pre-existing import was removed: all three public imports are used by the unchanged
statement. The original module had no proof-dependency imports to remove.

The following planned dependencies are no longer used by this item's proof route:

- `lem-pc-rf-single-complex-relative-mayer-vietoris`, module
  `Sheaf.AlgebraicGeometry.RelativeMayerVietoris`: replaced by the direct union comparison
  diagram and the two-out-of-three proof in the item.
- `lem-pc-single-complex-open-nested-comparison`, module
  `Sheaf.AlgebraicGeometry.SingleComplexOpenNestedComparison`: its invertibility-only
  transport is unnecessary. The new diagram node instead plans the actual arrow
  conjugacies using the already stated source-isomorphism theorem and coefficient
  coherence theorem.

Neither `Sheaf.AlgebraicGeometry.SingleComplexOpenUnion` nor the generic relative-MV
canonical-triangle/boundary/SES pipeline is imported. They remain available to other
users; this report does not claim they have become globally unreachable.
The pullback-QCoh preservation result and the comparison definition remain needed by
the new triangle node, so they are not claimed as mathematically pruned. Its generic
K-injective, exact-sequence, composition and coefficient-coherence dependencies are
listed in its DAG record.

## Where the brief, the DAG or earlier work was wrong

The parent DAG plan says to import `RelativeMayerVietoris`, but
`tools/import_direction.py may` refuses it: its source import closure already reaches
`SingleComplexOpenAffineUnion`. The same is true of `SingleComplexOpenUnion` and
`RelativeMVCanonicalTriangles`. This is an import-architecture issue, not a false
mathematical statement. The new module avoids these imports and does not adapt modules
held by other groups.

The cycle passes through RelativeMVCanonicalTriangles, RelativeMVBoundaryCompletion,
RelativeMVSESPresentation, RelativeMVConePresentation, RelativeMVPinnedTriangleComparison,
DerivedBaseChangeMayerVietorisBoundary, DerivedBaseChangeMayerVietorisMaps,
AffineGlobalHomBaseChangeMap and the coherator/perfect-representative/proper-flat chain,
ending in SingleComplexQcqsHomologyMono and this item. Thus merely reusing the already
proved general union argument would be circular at the module level.

The unit record `sk-thm-picard-coherence` has empty realized statement and step lists.
The source route is preserved: relative Mayer--Vietoris on the union followed by the
triangle two-out-of-three argument. No target, unit statement or unit step was changed.

The local literature checkout lacks the cited Stacks .tex files. The proof diagram and
functorial relative triangle were read at the authoritative online Stacks pages for
Tags 0DJ9, 08BV and 08HZ. LeanSearch returned Internal Server Error; LeanFinder and direct
Mathlib searches supplied generic short-exact triangle and sheaf-gluing declarations,
but no scheme-derived comparison diagram.

## New nodes

`lem-pc-single-complex-open-union-triangles`:
`lean/Sheaf/AlgebraicGeometry/SingleComplexOpenUnionTriangles.lean`, declaration
`AlgebraicGeometry.singleComplexOpenComparison_union_triangles`. This states only the
relative comparison diagram on a compact union, without any invertibility assumptions
or conclusion. Source: [Stacks Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
induction diagram, and [Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ), functorial
relative Mayer--Vietoris. The node records all three required search kinds, the exact
Lean signature, the source proof in steps, the parent chapter/unit and D2 creation data.
No change record is needed: no existing interface or definition changed.

## Second reading by D2

1. I compared `SingleComplexOpenAffineUnion.lean` with the repository version. The
   theorem signature, visibility, and existing declarations are unchanged; the only
   interface addition is the explicitly recorded proof-only import.
2. I compiled both delivered modules with `lcompile.py`; they compile cleanly. The
   affine-union theorem has only the permitted `sorryAx` dependency through the named
   split-off triangle theorem, and the triangle theorem contains its sole named `sorry`.
3. The split-off triangle statement is a strictly simpler, true construction statement:
   it asserts existence of the two triangles and their componentwise morphism, without
   assuming or concluding any component is invertible. Its source, docstring, and DAG
   node agree, and no duplicate declaration was found in the library.
4. The proof follows the shortest available route after the direct relative-Mayer--Vietoris
   modules were found to create an import cycle: compactness, the split-off construction,
   biproduct isomorphism, and the triangulated two-out-of-three lemma. The proof-only
   import and obsolete proof dependencies are recorded in `## No longer needed`.
5. The unit `sk-thm-picard-coherence` and its intended union-to-two-out-of-three route are
   preserved. The DAG proof steps and dependencies match the Lean proof, and the new
   node records the lower construction step.

I changed only the report by adding this second-reading record; no Lean statements or
definitions were changed during review.
