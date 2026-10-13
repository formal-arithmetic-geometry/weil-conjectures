## What changed

Prepared a reduction of `AlgebraicGeometry.GrpObj.invariantCoefficient_of_mixed_commutator`
without changing its signature. Added the proof-only import
`Sheaf.AlgebraicGeometry.GroupScheme.TwoParameterTranslationAction`, whose explicit
construction translates the universal point by a double-parameter point. Its named theorem
states the geometric four-operator section identity before any coefficient extraction.
The main module proves mixed-lift naturality, coefficient extraction, the square-zero
operator calculation, and the final comparison. The existing DAG proof route is refined.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.GrpObj.invariantCoefficient_of_mixed_commutator`
(node `lem-ag-mixed-translation-coefficients`). No sorry remains in the item module.
Added hole: `AlgebraicGeometry.GrpObj.twoParameterRightTranslation_commutator_app`
(node `lem-ag-two-parameter-translation-action`). This is a decomposition: one upper
hole is replaced by one strictly geometric lower hole, so the net hole reduction is zero.
The lower statement has neither t nor the hypothesis identifying its mixed lift with a
commutator. It states the full section operator formula before coefficient extraction;
the original module proves the extraction, naturality, and final comparison.

The previously missing `InvariantCoefficients.olean` is now published. Repaired two
elaboration errors in the preserved main proof: compare the product morphisms before
applying `Over.Hom.left`, and transport the dependent `appLE` proof through an explicit
universally quantified equality. Both sandbox modules compile, with the auxiliary
module's single named sorry as the only remaining hole. No existing signature changed.

## No longer needed

No imports removed and no planned modules pruned. The structural dependencies
`def-sc-group-scheme` and `def-sc-dual-numbers` remain necessary. The unit's route is kept.
The main proof does not use `invariantCoefficient_mul`, the faithful-additive theorem,
the tangent/Lie equivalence, or the bracket module; no imports of those proof results
were added.

## Where the brief, the DAG or earlier work was wrong

The DAG's two steps cite only structural definitions, not a stated geometric
coefficientwise pullback theorem. The new node makes that omitted geometric step
explicit; the remaining algebra and the application of the mixed-point equality are
separate Lean proofs. No existing mathematical statement or definition was changed.
The earlier missing-object blockage has resolved in the shared compiled snapshot.
The preserved proof had not compiled previously; its two glue errors are now fixed.

## New nodes

`lem-ag-two-parameter-translation-action`, in
`lean/Sheaf/AlgebraicGeometry/GroupScheme/TwoParameterTranslationAction.lean`, states the
full four-operator section formula for explicit universal right translation. The formula
is valid for empty schemes and arbitrary characteristic, since all constructions are
sheafwise and use only additive maps and square-zero parameters. It isolates the geometric
step while leaving the operator expansion and comparison to the original theorem.
No change record: existing public signatures, definitions, and visibility stay unchanged.

## Second reading by E4

1. Interface preservation — PASS. Compared the entire main module with the repository
   using diff. The existing theorem signature and docstring are byte-for-byte unchanged;
   the edits add four private proof helpers, one plain proof import, and its proof.
   The auxiliary module is new. No existing definition, hypothesis, conclusion, visibility,
   or target statement changes; no change record or forced adaptation is required.
2. Proof and axioms — PASS as a decomposition. Compiled both delivery modules in import
   order with lcompile.py (2.9 and 18.2 seconds, no errors or warnings). Compiled a scratch
   copy containing both modules' declarations with explicit #print axioms checks for all
   nine declarations. The definitions and four private helpers have only the permitted
   axioms (the section operators have none). The new geometric theorem and the main
   theorem additionally use sorryAx. The sole textual sorry is the complete proof of
   AlgebraicGeometry.GrpObj.twoParameterRightTranslation_commutator_app. There is no
   hollow definition, forbidden declaration, or arbitrary witness chosen from an
   unproved existence theorem. One old hole is closed and one new hole added: net zero.
3. Split statement — PASS. Read its construction, full signature, docstring proof, node,
   and source paragraph. The lower statement proves the geometric section formula with
   v,w only; it has neither t nor the mixed-lift equality hypothesis. The main proof
   separately establishes mixed-lift naturality, extracts the coefficient, proves the
   operator expansion, and compares the section maps. Thus this is a genuine reduction,
   not an application of a renamed original statement. Checked the order: right
   translation by a product composes translations in product order, and pullback puts
   the v operator outermost. Applying the four operators to a yields coefficients
   (a,0,0,D_v(D_w(a))-D_w(D_v(a))). For an identity point either operator is zero; for
   equal operators the mixed coefficient vanishes; characteristic two needs no division;
   on an empty scheme the section calculation is still valid. The argument is local on
   opens and needs no affineness or smoothness. Independent leanfinder, loogle, grep,
   and repository searches found no existing full section-map identity. Closing this
   geometric theorem requires formalizing parameter-preserving lifted translations and
   their composition; it is not a few-minute algebraic corollary.
4. Route and pruning — PASS. Reviewed InvariantCoefficients, the group-scheme translation
   results, the diagonal coefficient helpers, the InfPoints constructions, and the
   source Bracket module. None supplies a shorter proved geometric bridge. Both imports
   are necessary: InvariantCoefficients supplies the public signature and the auxiliary
   module supplies proof-only definitions and its geometric theorem. The added import
   correctly remains plain import. Both old proof_deps, def-sc-group-scheme and
   def-sc-dual-numbers, are still used; no old dependency or module is omitted from
   No longer needed. The sk-d-tangent unit record and its realized fields are unchanged,
   and its route is retained.
5. DAG agreement — PASS. The existing node records naturality, the geometric section
   identity, and the proved algebra/comparison in the same order as Lean. Its proof_deps
   are precisely the union of its steps' uses. The new node records the exact Lean
   statement, its explicit construction and operators, source, full proof, structural
   dependencies, provenance, blueprint origin, chapter/unit, and creation information.
   Its only remaining theorem hole matches the docstring and report.

Second reading changed no Lean code or mathematical statement. Added independent search
records (including a successful loogle search) to the new node and this review section.
Pruned none; the delivery remains explicitly a one-for-one decomposition.
