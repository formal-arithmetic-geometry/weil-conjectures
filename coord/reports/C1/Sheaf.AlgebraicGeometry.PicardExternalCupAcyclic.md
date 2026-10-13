## What changed

Removed the only sorry in `Sheaf.AlgebraicGeometry.PicardExternalCupAcyclic`,
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_of_acyclic`,
without changing its signature or its existing docstring. Added proof-only imports of
`Sheaf.Algebra.Homology.TensorKunnethNat`,
`Sheaf.AlgebraicGeometry.PicardExternalCupZeroTensor`, and
`Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic`.

The complete Lean reduction separates degree zero from positive degrees. In positive
natural degree every tensor Kunneth summand has a positive factor, so the factor
acyclicity assumptions kill the source homology; the geometric vanishing lemma kills
the target. In degree zero, evaluation and direct-sum induction identify the single
(0,0) summand with the entire direct sum. Surjectivity of the factor homology projections
lifts homology classes to cycles. The Kunneth cycle formula and the cochain normalization
identify the homology map with the transported geometric section tensor equivalence on
pure tensors. Tensor extensionality proves equality on all elements and gives bijectivity.

Added a proved private helper `modelHomology_subsingleton` for transporting the original
O-module cohomology vanishing through scalar restriction and `picardScalarModelEquiv`.
The two geometric steps are stated in their own new modules and nodes, each with its
source and a complete proof in words. The degree-zero statement requires no factor
acyclicity and says nothing about a cochain map. The positive-degree statement says
only that the product coefficient cohomology vanishes. Neither restates the target.

All three files compile together through lcompile.py with no warnings. The notation
scope is local to the proof, leaving all file-level commands unchanged. Every new Lean
line is at most 100 characters. No existing public signature, definition, visibility,
or public import was changed; no forced adaptations are needed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_of_acyclic`
(node `lem-sc-picard-external-cup-acyclic`). There are no sorries left in the item module.

Added two holes, each the complete proof of one public theorem:

- `AlgebraicGeometry.Scheme.Modules.picardExternalCup_zero_tensor`, in
  `Sheaf.AlgebraicGeometry.PicardExternalCupZeroTensor`, node
  `lem-sc-picard-external-cup-zero-tensor`.
- `AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_acyclic`, in
  `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic`, node
  `lem-sc-picard-external-coefficients-acyclic`.

This is a decomposition: one upper hole closed, two strictly smaller geometric holes
added; it is not a complete geometric proof or a net reduction of the sorry count.
The imported cochain existence theorem is not invoked: the proof handles the specified
map c using its normalization hc. Tensor Kunneth and the scalar model comparisons are
existing library declarations; no new algebraic holes were introduced.

The equivalences obtained inside the proof are local proof witnesses. The geometric
one is determined uniquely by its value on pure tensors, and the Kunneth equivalence
by its formula on tensor-cycle classes, since homology projections are surjective and
those classes generate. No definition chooses arbitrary data from mere unproved existence.

## No longer needed

No existing imports were removed. No modules or nodes are globally pruned: the geometric
parts of the original plan remain needed in the new geometric nodes. The original node
now directly depends on the two new geometric nodes, tensor Kunneth, the scalar models,
and cochain normalization. Its former direct dependencies on affine intersections,
affine spectra products, affine pullback sections, affine tensor sections, affine Cech
comparison, Cech/cup compatibility, the higher-direct-image presheaf, qcqs direct-sum
cohomology, and degenerate Leray now belong to the new geometric nodes. They have not
been claimed as eliminated work. Explicitly, the former direct dependencies absent
from the item's new `proof_deps` are:

- `lem-sc-picard-affine-diagonal-intersections`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `lem-sc-cech-comparison-map-iso-affine`
- `lem-sc-picard-cech-cup-pullback-compat`
- `lem-weil-pbc-higher-direct-image-presheaf`
- `lem-weil-pbc-qcqs-cohomology-direct-sum`
- `lem-pc-leray-degenerate-sections`

Each is retained in at least one new geometric node's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The listed geometric dependencies do not directly supply either the external-coefficient
vanishing statement or a degree-zero equivalence with the specified cup formula. The
new nodes state exactly these missing geometric conclusions, while the remaining
algebraic combination is fully proved here.

The local literature checkout contains the citation lists but not varieties.tex. I read
Stacks Tag 0BED at https://stacks.math.columbia.edu/tag/0BED. The source expressly says
that the tensor total of the two cover complexes is not isomorphic to the product-cover
Cech complex. The degree-zero node therefore uses two finite-cover sheaf equalizers,
not that false complex identification. The source leaves the final degree-zero cup
verification implicit; the new node spells it out using the affine pullback/tensor
formulas and the degree-zero cohomology/cup comparison.

Edge cases checked in the mathematical arguments: an empty scheme or zero coefficient
makes both section tensor spaces zero and all positive cohomology zero; a nontrivial
acyclic coefficient need not have finite-dimensional global sections, so the positive
proof uses arbitrary direct sums and no finite basis hypothesis. Degree zero is proved
without hF or hG; for n>0, p+q=n guarantees a positive factor. Non-separated schemes
are allowed provided the stated affine diagonals hold. The unit record for
sk-prop-av-cube has no realized node among these dependencies; its route is preserved.

Mathlib searches were run with msearch.py and are recorded in searches.jsonl. LeanSearch
returned Internal Server Error and is recorded as unavailable. LeanFinder returned
module tensor definitions and unrelated condensed-module statements, with no matching
geometric result. The Mathlib AlgebraicGeometry grep for kunneth|acyclic returned no
matches. Local searches of Sheaf, WeilConjectures, and the imported blueprint found no
independent lower declaration for either new geometric statement. Higher Picard Kunneth
results depend on this item and cannot be used without a cycle.

## New nodes

`lem-sc-picard-external-cup-zero-tensor` is the degree-zero section tensor equivalence
with its externalCup pure-tensor formula. Its own module is
`lean/Sheaf/AlgebraicGeometry/PicardExternalCupZeroTensor.lean`. Its proof uses affine
section formulas, finite-cover equalizers, and degree-zero cup comparison. It does not
assume positive-degree acyclicity and does not involve a normalized cochain map.

`lem-sc-picard-external-coefficients-acyclic` is positive-degree vanishing for the
external tensor coefficients. Its own module is
`lean/Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAcyclic.lean`. Its proof follows
the affine-basis calculation, higher-direct-image presheaf, arbitrary direct-sum
acyclicity and degenerate Leray argument of Tag 0BED. It does not assert an isomorphism
of comparison maps. No change records are required.


## Second reading by C1

1. Compared the complete item module with the repository using diff. The existing
   public signature and docstring are byte for byte unchanged; only the proof,
   a proved private helper, and three plain proof imports were added. No definitions,
   public imports or file-level commands changed. The two other modules are new.
   Verdict: no accidental interface change; no change record required.
2. Read the reduction and compiled all three modules in dependency order through
   lcompile.py without warnings. The only direct sorries are the two named geometric
   theorems listed above. No forbidden declarations or hollow definitions occur.
   The degree-zero witnesses are local to the proof, and their tensor formulas
   determine the equivalences; no arbitrary existential data enters a definition.
   Scratch-copy #print axioms on each delivered public theorem showed exactly
   propext, Classical.choice, Quot.sound and sorryAx; no other axiom occurred.
   Verdict: genuine algebraic reduction, conditional on the reported open geometry.
3. Read both split statements and their complete docstring arguments against
   Stacks Tag 0BED (https://stacks.math.columbia.edu/tag/0BED), and inspected the
   actual externalCup and scalar model definitions. The finite equalizer argument
   proves degree zero without acyclicity; affine-basis calculation and degenerate
   Leray prove only positive vanishing. Checked n=0 separately from n>0, empty schemes,
   zero coefficients, and infinite-dimensional sections. Repeated independent
   LeanFinder searches using box-product/sections and higher-cohomology wording,
   Loogle search for scheme modules and TensorProduct (zero hits), Mathlib grep for
   globalSections/tensor/boxProduct, and local rg for section tensor comparisons.
   Found generic tensor and sheaf tools, but no replacement geometric theorem.
   Existing Picard Kunneth results depend on this item, so are circular here.
   Verdict: true, needed, strictly smaller geometric statements; neither is a
   restatement. Their closure requires substantial geometry, not a short repair.
4. Read the Kunneth cycle formula, normalization hc, and the scalar model comparison.
   The singleton direct sum, surjective cycle projections and tensor extensionality
   give the degree-zero map equality; positive-degree source and target are zero.
   Each added import serves the proof and is plain. Existing public imports supply
   the statement and were retained. Listed every former direct dependency explicitly
   under No longer needed; each remains in a geometric node, so none is globally
   pruned. Inspected dag/units/sk-prop-av-cube.json: its realized arrays are empty,
   and no unit realization is bypassed. Verdict: shortest available algebraic route
   and honest decomposition accounting, with one hole closed and two added.
5. Compared node statements and recorded Lean signatures with the code, checked
   proof_deps against the union of proof step uses, and read the source, provenance,
   searches, creation and blueprint records of both new nodes. The original node
   records the actual Lean reduction and the new nodes record its remaining geometry.
   Verdict: metadata agrees; no target or unit statement changed.

Second reading changed the new vanishing theorem's proof docstring and node's final
step to spell out the Leray condition for every q (q=0 by direct sums, q>0 by zero
higher direct images). Expanded No longer needed to name all nine former direct
dependencies. The Lean reduction and all theorem signatures were left unchanged.
