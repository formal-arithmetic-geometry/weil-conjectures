## What changed

Replaced the sorry in `AlgebraicGeometry.derivedDirectImage_square_mate` with a complete
Lean reduction. For one composable pair, `Functor.rightDerived_ext` compares the mate's
unit equation with the selected direct-image composition comparison's unit equation.
`conjugateIsoEquiv` supplies the inverse equation. Equality transport follows by
substitution and `conjugateEquiv_id`; two applications of `conjugateEquiv_comp` then
assemble the original square. The existing definition and theorem signatures are unchanged.

Added the proof-only import `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit`.
Its one public theorem isolates the remaining single-pair unit-normalization step of
the existing proof plan. The parent's DAG proof and dependencies now describe this reduction.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.derivedDirectImage_square_mate`
(node `lem-sc-derived-direct-image-square-mate`). There are no sorries in the item's module.

Added one hole: `AlgebraicGeometry.derivedPullbackComposition_mate_unit`
(node `lem-sc-derived-pullback-composition-mate-unit`). This is a decomposition, not a net
hole reduction: one hole closed and one added. The new statement concerns just two
composable maps and their unit equation, without a commutative square, comparison to a
chosen direct-image composition isomorphism, inversion, or equality transport. The
right-derived uniqueness and square-assembly steps are fully proved in the item.

Both delivered modules compile locally through `lcompile.py` within its single-file limit.
The new equation was checked on identity morphisms, zero complexes and empty schemes;
it imposes no geometric or boundedness hypothesis.

## No longer needed

No imports were removed and no whole modules are claimed pruned. The old direct
proof edges to `def-pc-derived-base-change-map` and
`lem-pc-ringed-spaces-derived-pullback-composition` are replaced by their use through
`lem-sc-derived-pullback-composition-mate-unit`; both remain transitive dependencies. The direct proof edge
to `lem-pc-ringed-space-direct-image-kinjective-acyclic` is unnecessary: the item now uses
right-derived uniqueness directly. That node remains a transitive dependency of
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`, so this is not a
claim that it leaves the targets' closure. The pinned pullback composition and adjunction
nodes remain needed through the new normalization lemma.

## Where the brief, the DAG or earlier work was wrong

The plan can replace its explicit cancellation on K-injective representatives and
resolution transport with the universal property of the single right-derived functor.
The source-library `rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv` is not directly
applicable: its exact-left-adjoint and K-injective-preservation assumptions are absent here.
No statement was weakened and no unit route was changed.

The blueprint ancestor tool reports no imported ancestor for the item's module-created
node. The new node therefore records `blueprint.from.node = null` and identifies the
precise parent proof clause in `from.place` and `via`, rather than inventing a blueprint
ancestor. The Stacks pages 079W, 0D5S and 0D5T were read online. LeanSearch returned a
service error; LeanFinder, Loogle, grep and local source inspection were completed.

## New nodes

`lem-sc-derived-pullback-composition-mate-unit` is the single-pair normalization equation,
stated in `lean/Sheaf/AlgebraicGeometry/DerivedPullbackCompositionMateUnit.lean`. Its node
and docstring give a proof by transposing the selected left-derived counit equation under
the pinned Hom equivalences and pasting mates. No new data is chosen and no existing
interface is changed. There are no change records or forced adaptations.

## Second reading by R3

1. Interface: PASS. Compared the whole item with the repository using diff. Its only
   changes are a private proof import and replacement of the original theorem's sorry
   by a proof. All existing declaration signatures and the comparison definition are
   byte-for-byte unchanged. There are no forced adaptations or change records.
2. Proof and axioms: PASS as a decomposition. Both modules compile with lcompile.py.
   Separate scratch copies print axioms for both item declarations and the new lemma.
   The comparison definition uses only propext, Classical.choice and Quot.sound; the
   square theorem and split lemma additionally use sorryAx. The only delivered sorry
   is the public named theorem derivedPullbackComposition_mate_unit. There are no
   forbidden declarations, proof holes inside definitions, or arbitrary new data choices.
   rightDerived_ext identifies transformations out of the single derived functor;
   Iso.ext and inverse projection give hi; equality elimination proves he; mate
   composition supplies the correctly oriented three-factor square.
3. Split statement: PASS. Read the actual characterization of p in
   exists_derivedPullbackComposition and the actual Hom normalization in
   exists_schemeDerivedAdjunction. They pin the choices used here and give the unit
   equation by transposing the counit factorization. The statement covers one pair
   and one unit equation, strictly below the square's uniqueness, inverse,
   equality-transport and assembly steps. It is not a renamed square assertion.
   For identities the chosen counits may be nontrivial, but their normalization
   cancels any adjunction twist; for zero complexes both composites are zero; for
   empty schemes the same categorical argument applies. No exactness or K-injective
   preservation has been assumed. Read Stacks 079W, 0D5S and 0D5T independently.
   New searches used Loogle for mateEquiv with comp, LeanFinder for right-derived
   units as mates of left-derived counits, and rg for unit/mate and conjugate/unit
   terminology in Sheaf, Mathlib and the source library. Only generic pasting tools
   were found. The source CompConjugate theorem requires exact left adjoints and
   K-injective preservation, which are unavailable for general tensor pullback.
   Closing the remaining lemma requires a substantial localization/mate calculation,
   not a few-minute application of an existing theorem; it is left explicitly open.
4. Route and pruning: PASS. The proof follows the single-pair normalization of the
   old plan and uses the shortest available uniqueness argument. Both original
   public imports occur in existing signatures or the existing definition, and the
   new proof import is private. Read sk-thm-picard-duality.json: realized.statement
   and its sole realized step are empty, so no realized unit node is bypassed.
   All removed direct proof edges are now listed, with their retained transitive
   uses distinguished; no module is claimed pruned. Net holes closed minus added: 0.
5. DAG: PASS after clarification. The parent changes only proof, proof_deps and
   proof_origin. Its steps match hc, hi, he and final conjugateEquiv_comp rewrites.
   The new node has its verbatim Lean signature, source, proof, search records,
   creation record, blueprint provenance, chapter, unit and Lean record. Its
   proof_deps equals the union of its steps' uses. Clarified the roof extension in
   its final proof step and recorded K-flat resolution and pullback preservation.

Second reading changed the new lemma's docstring to explain extension of the pinned
Hom formula through localization roofs, its matching DAG proof/dependencies, and
report.md to list every removed old direct proof edge. No Lean statement, definition,
or proof term was changed. Scratch axiom-check modules are removed before delivery.
