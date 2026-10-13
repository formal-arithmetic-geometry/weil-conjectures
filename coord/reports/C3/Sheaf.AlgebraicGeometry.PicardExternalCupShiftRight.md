## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight` with a complete Lean reduction.
The existing public signature and public imports are unchanged. Added four proof-only imports:
`PicardExternalCupRightShortExact`, `QuasicoherentAcyclicEmbedding`,
`Modules.QuasiCoherentCokernelImage`, and
`CategoryTheory.Abelian.RightDerived.FullLongExactSequence`, all under `Sheaf`.

The proof gives Y its prescribed structure map g, applies the existing acyclic embedding,
and constructs the actual categorical cokernel Q. A proved private helper
`moduleCohomology_cokernel_isZero` uses the existing right-derived long exact sequence:
exactness at H^p(Q), together with vanishing of its two neighbors, makes H^p(Q) zero.
The inequalities needed to reduce the successor bound to bound d are proved with `omega`.
The proof obtains normalized realizations for E and Q, applies the supplied induction
hypothesis separately to both, and applies a short-exact comparison transfer.
All existential witnesses are eliminated inside proposition proofs; no definition or
persistent data is selected from an unproved existence statement.

Added two modules. `PicardExternalCupRightShortExact` proves the transfer by applying
Mathlib's categorical five lemma to an exact ladder, then cancelling the two comparison
isomorphisms. `PicardExternalCupRightExactLadder` isolates the geometric construction
and identification of that ladder as the sole new unfinished statement. It contains
neither a cohomological bound nor the induction hypothesis of the original item and
asserts an exact comparison diagram rather than invertibility of its middle arrow.
The embedding, bound reduction, applications of induction, five lemma, and conjugation
cancellation are real Lean proofs outside that remaining geometric statement.

Compiled all three delivery modules in import order using `lcompile.py --all`, with no
errors or warnings. The original module and the proved short-exact transfer have no
`sorry`. Updated the original DAG proof and added the two matching new nodes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_shiftRight`
(node `lem-sc-picard-external-cup-shift-right`). No `sorry` remains in the item module.

Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_of_right_shortExact`
(node `lem-sc-picard-external-cup-right-short-exact`) from the geometric ladder and
Mathlib's five lemma. The private cokernel-cohomology helper is fully proved from the
existing long exact sequence declaration.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_right_exact_ladder`
(node `lem-sc-picard-external-cup-right-exact-ladder`), in its own new module, with
proof exactly `by sorry`, source, and complete proof in words in its docstring.
It covers affine Cech exactness, the natural signed cup ladder, and normalization
on tensor-cycle spanning classes. The induced five-lemma conclusion is already proved.

This is a decomposition: one original hole closed and one new hole added, so no net
hole reduction is claimed. The theorem still depends on existing unfinished library
lemmas, notably normalized cochain existence; these are existing items, not newly added
holes. Kernel validation here does not establish sorry-free axioms for the target closure.

Checked edge cases against the statements and source: d=0 only requires vanishing at
p>0 for E and Q, and imposes nothing on H^0(Q); n=0 uses two initial zero objects in the
comparison ladder. Zero coefficients and empty schemes give zero objects and zero
complexes, with the unique maps between zero homology objects invertible. No nonempty
scheme, nonzero coefficient, positive n, or positive d is assumed by a new theorem.

## No longer needed

No module is pruned from the targets' closure. No import was removed from the original
module. The second reader removed the redundant
`Mathlib.Algebra.Homology.ShortComplex.ShortExact` import from both new modules; its
declarations are already available through `PicardExternalCupCochain`. The original direct proof dependencies describing affine
Cech comparisons, affine product sections, cup compatibility, resolution models,
affine-intersection vanishing, and tensor Kunneth are now dependencies of the new
exact-ladder node, rather than direct dependencies of the bounded shift node. They
remain mathematically needed; this relocation is not pruning. The old direct proof dependencies no longer used directly by the shift node are:
`lem-sc-cech-comparison-map-iso-affine`,
`lem-sc-cech-comparison-map-naturality`, `lem-sc-cech-comparison-natural`,
`lem-sc-picard-affine-diagonal-intersections`,
`lem-sc-picard-cech-cup-pullback-compat`, `lem-sc-picard-kunneth-resolution-model`,
`lem-sc-qcoh-cech-total-tensor-nat-iso`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`,
`pqf-def-coherent`, and `pqf-lem-affine-vanishing`.
The geometric statements remain on the exact-ladder node's route; quasi-coherence
remains a statement dependency. This is dependency relocation, not pruning.
The unit `sk-prop-av-cube` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan did not provide a Lean declaration assembling the geometric
short-exact external-cup comparison ladder. Its stated dependencies give the component
comparisons and cup formulas, but do not immediately supply this ladder on the fixed
scalar models. That precise step is the remaining new theorem. The bound calculation
and the categorical diagram chase did not require additional unfinished statements.

This machine lacks the untracked Stacks and blueprint literature checkout named by the
node. Read the recorded unit JSON and the official source at
https://stacks.math.columbia.edu/tag/0BED instead. Its short-exact sequence paragraph
and the subsequent right-variable argument give exactly this reduction. No source or
statement error was found. LeanSearch returned Internal Server Error; LeanFinder,
Loogle, and source searches were usable and are recorded in both new nodes.

The existing long-exact sequence and quasi-coherent cokernel-image nodes are generic
tools from other units, used solely for the cokernel bound and closure under cokernels:
`lem-weil-pbc-derived-functor-long-exact` and
`lem-weil-pbc-quasi-coherent-module-cokernel-image`. The comparison uses the Mathlib
leaves `lem-weil-pbc-complex-ses-homology-long-exact` and `lem-weil-pbc-five-lemma`.
These uses preserve the original unit argument and need no changes to another module.

## New nodes

`lem-sc-picard-external-cup-right-exact-ladder`:
`Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder`, declaration
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_right_exact_ladder`.
States the exact five-term comparison diagram with the middle-map identification and
outside-arrow invertibility under invertibility for the other two coefficients.
This is the single split-off hole, independent of bounds or induction.

`lem-sc-picard-external-cup-right-short-exact`:
`Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact`, declaration
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_of_right_shortExact`.
Proved by the existing categorical five lemma and cancellation of comparison
isomorphisms. It is the exact-sequence transfer used by the original bounded shift proof.

No change records: no existing statement, definition, signature, or public import changed;
no other group's module was adapted.


## Second reading by C3

1. **Unchanged interfaces: pass.** Compared the original shift module with the
   sandbox using `diff` and separately compared the complete theorem signature
   byte for byte: identical. Its public imports, definitions, visibility, assumptions
   on k, compactness, affine diagonals, F and G, bound d, universal induction hypothesis,
   normalization hc and conclusion in degree n are unchanged. The two other modules
   and their nodes are new. No forced adaptation or change record is needed.
   The initial comparison inadvertently used `git diff --no-index`; it was read-only,
   and subsequent comparisons used plain `diff`.

2. **Proof and trust: pass as a decomposition.** All three modules compiled cleanly
   through `lcompile.py --all`. Inspected every declaration: only the new named
   `picardExternalCupCochain_right_exact_ladder` contains `sorry`; no prohibited
   declarations or hollow definitions occur. Explicit axiom probes for the shift,
   short-exact transfer, ladder and private cokernel helper show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from unfinished statements.
   The helper uses exactness of H^p(E) -> H^p(Q) -> H^(p+1)(G), not exactness at E.
   For d<p, p is positive and d+1<p+1, so both neighboring objects vanish.
   E is eliminated inside a proposition proof and Q is the actual cokernel; neither
   is data in a definition chosen from an arbitrary unproved existence assertion.
   The five-lemma implementation uses epi at index 0, iso at 1 and 3, and mono at 4,
   then cancels eB.inv and eA.hom with the corresponding Mathlib lemmas.

3. **New statements and searches: pass.** Read the official Stacks Tag 0BED
   (https://stacks.math.columbia.edu/tag/0BED), especially the exact-sequence argument
   after equation the project server and its application to the right variable. Matched its
   field, quasi-compactness, affine diagonal and quasi-coherence hypotheses with
   both new signatures. The remaining ladder is the geometric exact-sequence step;
   it has no bounds or induction premise, and leaves the embedding, cokernel bound,
   induction and diagram chase outside the hole. It is not a renamed shift theorem.
   In degree zero the five-term segment is 0 -> 0 -> H^0(S.X1) -> H^0(S.X2)
   -> H^0(S.X3); no surjectivity of its last arrow is required. For d=0 the bound
   only asserts vanishing for positive p. Zero F, zero coefficient sequences and
   empty schemes give zero homology terms; no excluded case was found.
   Normalization determines the homology map because `tensor_kunneth_nat` supplies
   spanning tensor-cycle classes and homology projections from cycles are surjective.
   Affine Cech exactness is justified by affine vanishing; coefficient refinement
   and cup naturality are present in `Sheaf.Paper.CechCupPullbackCompat`.
   Long-exact connecting-map naturality follows from a morphism of short exact
   complexes, not merely from separate naturality on cohomology groups.
   Repeated searches with different wording using LeanFinder, Loogle and grep:
   found `HomologicalComplex.HomologySequence.δ_naturality`, but no existing geometric
   external-cup ladder in Mathlib, upstream or lean/Sheaf. Upstream external products
   in etale/pro-etale derived categories concern different coefficients. The existing
   naturality and five-lemma results provide components, not the unfinished assembly.
   Closing that geometric assembly is not a few-minute repair.

4. **Route and imports: pass after cleanup.** The original acyclic-embedding and
   right-variable dimension-shifting route from 0BED is preserved. The cube unit
   file was read: its existing `realized` fields are empty (`statement: []`,
   `steps: [[]]`), a pre-existing metadata gap, and this delivery changes none of them.
   The proof retains the unit's cube argument and only decomposes a subordinate
   Kunneth reduction. Proof-only dependencies use plain imports; the new ladder's
   ExactSequence import supplies types in its public signature. Removed redundant
   ShortExact imports from the two new modules and compiled again. Expanded
   `No longer needed` to name all twelve old direct proof dependencies removed from
   the shift node, without claiming that their modules leave the target closure.

5. **DAG and Lean: pass after wording repair.** The shift node's steps and union
   of uses follow its embedding, bound, normalized-existence/induction and transfer
   proof. The transfer node cites the exact ladder and Mathlib five lemma; its final
   cancellation is elementary. The ladder's three steps describe affine exactness,
   natural signed cup/connecting maps, and normalization via tensor-cycle spanning.
   Both new nodes have sources, searches, creation data, blueprint ancestry, chapter,
   unit and verbatim Lean signatures. Removed the ladder node's sentence asserting
   that the existential rows themselves include initial zeros: that choice is used
   in the natural-language construction, but is not separately asserted in Lean.
   This aligns the new node's statement with its signature without changing Lean.

Changes by the second reader: two redundant imports removed, exact-ladder node
wording aligned with Lean, and complete dependency relocation and independent review
recorded. One original hole is closed, one geometric hole is added: net zero.
