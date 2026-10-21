# Stage-1 report: lem-sfb-unit-tensor-braiding

## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-unit-tensor-braiding.json — statement, split into four explicit steps; no exact whole-item Mathlib match. Uses the existing Mathlib leaf lem-sfb-braiding-naturality. No new nodes or new Mathlib leaves.
- citations.json — the verbatim displayed equation from that leaf for step 2, the only node citation in the proof.
- searches.jsonl — the unmodified log written by the prescribed msearch.py commands. The item's inherited Q22 searches remain intact; the actual NB searches and their results are appended to mathlib_searches.
- report.md — this report and author's review.

## Attachments

None. The project source search for the blueprint tag and item id gave no hit. Searches for unit-tensor, LaxBraided.braided, and braiding naturality found related declarations, which I read: CategoryTheory.Adjunction.leftAdjointOplaxMonoidal_δ_braiding in WeilConjectures/CategoryTheory/Monoidal/Braided/Adjunction.lean:35, the adjunction declarations in WeilConjectures/Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean:83,104,115, and the pairing declaration in WeilConjectures/WeilSheaf/TensorObjPairing.lean:35. These concern the left adjoint's comparison, the right adjoint's braided axiom, or compatible endofunctor pairings. None states the item's arbitrary arrows X → RP and Y → RQ and all its conclusions. A calculation occurring inside a proof is not a declaration attachment.

## WANTED

None. The blueprint proof and the Mathlib source required here are present locally.

## What was wrong or incomplete

The imported item was a correct, self-contained statement with no proof. I preserved its statement, statement dependency, source, creation metadata and blueprint ancestry. The proof previously hidden in the parent's sentence about naturality is now explicit, with the actual input arrows and composition order. There is no statement dispute, coefficient-category identification, or departure from the unit route. The only generic tool is the existing Mathlib braiding-naturality leaf, so no new task or duplicate is necessary.

## Unfinished work

None for this one-level stage-1 split. No Lean was written and no compiler, Lake or build command was run. The required delivery command runs the server checks; the prohibited local check scripts were not invoked.

## Not duplicates

No new nodes. I searched the whole DAG and blueprint for braiding, braided, lax braided, and unit tensor, and read the existing braiding-naturality leaf. The parent lem-sfb-finite-upper-star-braided proves the strong symmetric monoidality of a particular inverse image; the point analogue lem-sfb-point-upper-star-braided concerns its particular inverse image. Neither is a statement of the arbitrary-arrow calculation of this item. lem-sfb-braiding-naturality states exactly the naturality equality required in step 2, and is reused rather than recreated. No blueprint statement found is equivalent to the whole generic item, so blueprint.same_as remains empty.

## Review by NB

I read the current chapter and unit records and the first paragraph of literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-finite-pushforward-pullback/lem-sfb-finite-upper-star-braided.proof.md. That paragraph uses precisely two inputs: compatibility of the right adjoint's lax comparison with braiding and naturality of braiding. The item's statement already assumes the first, and the existing leaf provides the second. The unit's second step asks for the same symmetry compatibility; this split stays below that step and does not alter the chapter or unit. The item's original blueprint.from.place already identifies the correct paragraph, so I retained it. There are no new-node sources to review.

For step 1 I checked the displayed braided hypothesis in the item's statement itself. Precomposing it with u tensor v gives an equality with source X tensor Y. Expanding a only reassociates three compositions; no functor being strong, symmetry of the braiding, inverse comparison, or adjunction compatibility is being inferred here. Therefore this step is elementary and needs no cited theorem beyond the hypothesis.

For step 2 I opened and read the entire statement of lem-sfb-braiding-naturality, and checked its Mathlib match against Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean:121–124. Its variables f:X→Y and g:X'→Y' specialize to u:X→RP and v:Y→RQ. The equality it states is exactly beta(RP,RQ) after u tensor v equals v tensor u after beta(X,Y). This is the sole non-elementary input; it is cited, not taken from the proof of another node. citations.json copies the displayed formula verbatim. The ambient monoidal-category definition was also read, including its tensor notation and composition convention; its recorded Stacks source is Tag 0FFK, categories.tex, definition-monoidal-category, and its following chosen-unit paragraph. The existing leaf is Mathlib, so its other unit creates no route substitution.

For step 3 I substituted step 2 into step 1 and checked that m(Q,P) is composable on the left. The resulting m(Q,P) after v tensor u is exactly b. All maps end in R(Q tensor P). This is substitution and associativity, not an unproved transport or hidden comparison, and is marked elementary. For step 4 the types of the unit components are precisely X→R(LX) and Y→R(LY), so specialization is legitimate for any stated adjunction. Naturality of the unit, its triangular identities, and any monoidal structure on L are not additional requirements. The proof explicitly supplies this final clause.

I checked small cases: u and v identities reduce to the assumed braided equation; the identity functor with identity lax comparisons reduces to braiding naturality; a general nonsymmetric braided category is allowed because no beta(Y,X) beta(X,Y)=1 is used. No morphism is canceled and neither u, v nor m is required invertible. Thus there is no missing faithfulness, symmetry or strong-monoidality hypothesis.

Against delivery-errors B1–B10: no unsplit new node, undefined new object, duplicate or fabricated leaf was introduced; the statement is self-contained using the existing monoidal-category definition and inline braided/lax/adjunction data. TeX is single-escaped after JSON decoding. No new Stacks claim needs a tag. All retained inherited search metadata is preserved as received; all appended searches were actually run by msearch.py and their results were read. In Mathlib I read the braided field at Basic.lean:386–388, braiding_naturality at 121–124, and the candidate surrounding constructions: the field is the hypothesis, not the composite conclusion. A second semantic phrasing was run before deciding against a whole-item match. No sorry-free project declaration states the entire item. Blueprint searches found no whole-item duplicate.

Against C1–C8, D1–D5 and E1–E7: the only theorem application is covered by its exact cited statement, with all its hypotheses verified above. The other steps are explicit elementary equality manipulations, and no tag is used as a substitute for a node. proof_deps is exactly the union of uses. The proof depends only on the old naturality leaf and hence cannot cycle through its parent. No clause was moved into a new restatement, no induction or omitted standard comparison is hidden, and no unreported off-route lemma or source correction was used. I checked the source/target objects and ordinary versus Lean diagrammatic composition order. There are no non-elementary steps exceeding 2000 characters (the longest step is 354 characters), and no unresolved mathematical issue.
