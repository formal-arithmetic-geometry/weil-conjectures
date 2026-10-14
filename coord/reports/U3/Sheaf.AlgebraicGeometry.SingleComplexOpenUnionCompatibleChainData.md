## What changed

Completed the earlier attempt in
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnionCompatibleChainData`.
The proof restricts the square and the given coefficient map to W = U union V,
uses `AlgebraicGeometry.relativeMV_cover_rows` on the resulting two-open cover,
and turns its two short exact rows into compatible cone models with Mathlib's
`CochainComplex.mappingCone.quasiIso_descShortComplex` and
`CochainComplex.mappingCone.map_descShortComplex`.
A proved private helper constructs nested comparison arrow isomorphisms using
`AlgebraicGeometry.exists_derivedBaseChange_source_iso` and
`AlgebraicGeometry.singleComplex_nested_coefficient_coherence`.
Biproduct projection extensionality combines and transports the middle equations.
The statement, universes, hypotheses, and existing public imports are unchanged.
The existing quasi-coherence and compactness hypotheses remain named and are
explicitly retained in the proof context; the cover-row argument works more generally.
The node's proof, proof_deps and proof_origin now describe this route.

The module adds only proof imports:
`Sheaf.AlgebraicGeometry.RelativeMVCoverRows`,
`Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceIso`,
`Sheaf.AlgebraicGeometry.SingleComplexNestedCoefficientCoherence`,
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`, and
`Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.singleComplexOpenComparison_union_compatible_chain_data`
(node `new-single-complex-open-union-compatible-chain-data`).
The private `nested_arrow_iso` helper is proved.
No holes remain in this module; no holes or new theorem modules are added.
This is a proof from existing named statements, including the still-open
`AlgebraicGeometry.relativeMV_cover_rows`
(node `lem-pc-relative-mv-cover-rows`); it is not a claim that its transitive
axiom closure is already sorry-free.

The unit `sk-thm-picard-coherence` has no realized statement or proof-step nodes;
its route is preserved. Empty or repeated opens still form the same two-open
cover of W; no nonemptiness, distinctness, flatness or coefficient-isomorphism
assumption was introduced.

## No longer needed

Removed the earlier sandbox attempt's unused proof imports:
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnitNaturality`,
`Mathlib.CategoryTheory.Adjunction.Mates`, and
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`.
Removed its unused private `top_arrow_iso` helper: the global cover-row arrow
is definitionally the required ambient comparison on W.

The node no longer directly cites:
`prop-pur-kinjective-resolutions-exist`
(`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`),
`lem-pc-open-union-image-complex-exact`
(`Sheaf.AlgebraicGeometry.OpenUnionImageComplexExact`),
`lem-pc-homotopy-square-cone-rectification`
(`Sheaf.CategoryTheory.DerivedCategory.HomotopySquareRectification`), and
`lem-pc-derived-direct-image-composition`
(`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`).
The resolution and direct-image-composition modules remain transitive dependencies
of the cover-row theorem. The open-union exactness and homotopy-square rectification
modules are absent from this item's new import closure. Other target routes may
still need them; this delivery does not assert global unreachability or delete them.
No existing public import was removed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt did not compile: its declaration docstring preceded
scoped options, it tried to use nonexistent `biprod.map_comp`, its simplification
steps did not unfold local arrow definitions at the needed transparency, and its
final component equations remained unfinished. The present proof repairs these
issues and uses the existing cover-row theorem rather than duplicating its
resolution and strictification construction.

The initial attempt also contained an unnecessary top-open arrow-transport helper.
The global row after restriction is already exactly the comparison on U union V.
No statement or definition correction, forced adaptation, or new node is needed.

Searches: the earlier recorded LeanFinder homotopy-square query and Loogle arrow
query were checked; fresh LeanFinder and Loogle searches found the Mathlib
short-exact-to-cone comparison and its naturality. Grep of Mathlib and both library
roots confirmed the existing cover-row theorem and the two coefficient/source
transport declarations used here. No exact finished geometric theorem was found.

## Second reading by U3

1. PASS: Compared the sole delivered module against the repository with `diff`;
   independently extracted the existing theorem signature and checked it byte for
   byte. Universes, binders, hypotheses, conclusion, visibility and all existing
   public imports are unchanged. No definitions or change records are added.
2. PASS: Compiled the delivered file through lcompile.py without errors or
   warnings. Scanned the complete module: no sorry, axiom, unsafe, opaque,
   implemented_by, extern or hollow definition. The scratch-copy axiom check
   is recorded below. Existential row and transport witnesses are used inside
   a theorem proof; no arbitrary witness supplies public definition data.
3. PASS: No statements or holes were split off. Read the existing cover-row,
   source-isomorphism and nested-coefficient declarations. The cover-row
   hypothesis is satisfied by inverse-image opens covering W; empty, equal,
   contained opens and zero coefficients require no new condition. The private
   helper is proved from canonical open/pullback isomorphisms and coefficient
   coherence. Fresh Loogle search for mappingCone.map_descShortComplex confirmed
   the exact Mathlib naturality identity used; rg across both library roots
   found no shorter finished theorem for this strict geometric statement.
4. PASS: The cover-row reduction retains the prescribed coefficient morphism
   at all three vertices. The existing RelativeMVCoverHomotopyData theorem
   only returns a homotopy square, so it does not replace this strict-square
   construction. Each added proof import supplies a used declaration; existing
   public imports remain required by the signature. Checked every removed old
   proof dependency against No longer needed. The unit's realized statement and
   sole proof-step lists are empty; no designated unit node is bypassed.
5. PASS: Compared the node diff and read all proof steps. Only proof,
   proof_deps and proof_origin change. Their three named dependencies match
   the cover-row application and helper; the remaining cone/biproduct
   calculations use Mathlib. The recorded statement still matches the Lean.

Second reading changed only this report, adding the independent review.
No repair to the Lean proof or DAG was needed. One original hole is closed,
zero holes are added, and zero statements are split off.

Scratch-copy `#print axioms` verdict: nested_arrow_iso uses exactly propext,
Classical.choice and Quot.sound. The main theorem uses those three plus
sorryAx through existing open dependencies (in particular relativeMV_cover_rows);
there is no new direct hole. The scratch copy compiled without warnings in
43.6 seconds; the delivered module compiled in 45.0 seconds.
