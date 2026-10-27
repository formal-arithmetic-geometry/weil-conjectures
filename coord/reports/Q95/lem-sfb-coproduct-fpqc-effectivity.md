# Q95 stage-1 report: lem-sfb-coproduct-fpqc-effectivity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-coproduct-fpqc-effectivity.json: item, now split; statement unchanged; no Mathlib match for its full conclusion.
- citations.json: verbatim statements backing every step/node pair.
- searches.jsonl: five actual searches made through msearch.py, with returned types read.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. All supporting statements already exist.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id, ind-quasi-affine terminology, coproduct/fpqc combinations and effective descent found no declaration stating all clauses. AffineFlatDescent.lean proves affine descent, which cannot apply to an infinite coproduct merely because its components are affine. InvariantOpenEffectiveDescent.lean glues effective open data but does not by itself assert this item's existence conclusion. Neither is an attachment.

## WANTED

None. All sources used are present locally.

## What was wrong

The item was statement-only; its statement already corrects the blueprint's infinite quasi-affine assertion. The unit's step 4 and det-lem-stratified-lattice-scheme proof (2) call an arbitrary union of copies of an affine scheme quasi-affine. Under the quasi-compact convention fixed in this item, that is false: take infinitely many copies of Spec(k) for a nonzero field k; their disjoint nonempty open components form a cover with no finite subcover. Their union embeds openly into Spec of the product ring, but it is not quasi-compact. No statement correction to this item is needed: it explicitly asks for finite-component containment of each quasi-compact open and then Tag 0APK effectivity, not quasi-affineness of the whole infinite union. The proof follows that already corrected route.

The general theorem lem-a1-ind-quasi-affine-fpqc-effective-descent already states exactly the required effectivity criterion. Creating another 0APK node would duplicate it. The finite-component and open-restriction clauses are short arguments from existing statements, not new nodes.

## Unfinished work

None at stage 1. No Lean was written and no compiler, Lake or build tool was run.

## Review by Q95

I read the chapter sec-six-functors-basics and unit sk-lem-stratified-lattice, and the current main-20261015 proof of det-lem-stratified-lattice-scheme, especially (2). I read Stacks more-morphisms.tex at Tag 0AP6 (definition-ind-quasi-affine) and its alternative-definition criterion, and more-groupoids.tex at Tag 0APK (lemma-ind-quasi-affine, statement and beginning of the proof). The latter takes an fpqc covering and an ind-quasi-affine scheme descent datum, with no quasi-compactness requirement on the total morphism. This is the unit's original 0APK tool, not a replacement proof route. No SGA source is used. There are no new nodes whose source needs separate review.

For step 1, I opened the actual statements of def-weil-open-immersion, def-pc-fibre-product and lem-weil-pbc-scheme-coproduct-family. The first identifies an open immersion with the restricted sheaf on its open image; the second gives the representing universal property; the third gives disjoint open components and their mapping property. Thus an open component pulls back to B and componentwise inverse maps glue over the empty overlaps. The text includes this argument rather than citing the finite-family base-change/coproduct lemma for an infinite family; that lemma would have had an insufficient hypothesis for this use. This step is elementary from the cited definitions and coproduct statement.

For step 2, I read def-weil-pbc-quasi-compact-scheme and used its finite-subcover definition on the component intersections with K. I read the coproduct statement again for the open finite union, and clause (4) of lem-weil-pbc-affine-morphism-permanence, which explicitly states that a finite disjoint union of affine schemes is affine. Thus there is no unproved affineness assertion hidden in the step. I also read Mathlib/AlgebraicGeometry/Limits.lean:651, the finite-family IsAffine instance, confirming the existing leaf used for this clause. This step is a finite-subcover argument plus the quoted leaf, not an independent lemma.

For step 3, I opened lem-weil-pbc-affine-scheme-qcqs: its statement explicitly gives both quasi-compactness of affine schemes and quasi-compactness of intersections of two quasi-compact opens in an affine scheme. D is affine by step 2. Its open D' is affine by the same finite-coproduct clause. Hence K and D' are both quasi-compact opens of D, so their intersection is quasi-compact. This avoids the false claim that an arbitrary open restriction of a quasi-compact space stays quasi-compact. I opened def-nagata-quasi-affine-morphism: it requires the inverse image of every affine target open to be a quasi-affine scheme. Step 3 verifies exactly that quantifier for all affine B' inside B, with the explicit quasi-compact-open-in-affine convention supplied in the item. Open restriction and its intersection description are the calculation already established in step 1.

For step 4, I opened the full statement of lem-a1-ind-quasi-affine-fpqc-effective-descent. Substituting A=V, B=X and its total V=T gives exactly the hypotheses in force: singleton fpqc covering from the item, its arbitrary scheme descent isomorphism and cocycle, and the universally quantified quasi-affine-open property proved in steps 1--3. Its conclusion is a scheme Y over X with the datum-compatible base-change isomorphism required here. The node explicitly imposes no quasi-compactness or finite-presentation hypothesis on T/V. I recorded this off-unit generic theorem as split_report.tool_uses; it is the Stacks 0APK theorem demanded by the unit itself.

I tested S empty, S a singleton, S infinite with V=Spec(k), V empty, and K empty. For K empty one can choose J empty; the finite coproduct is Spec(0), so both restriction and quasi-affine assertions hold. Infinite S with nonempty V shows why only K, not all of T, receives finite-component containment. If V is empty, the fpqc condition forces X empty (its affine opens must be covered by empty images); both the input and descended schemes are then empty. The general theorem includes these cases, so the proof needs no extra nonemptiness hypothesis. None of the cited nodes depends on the item, and no new dependency points back to the item.

I checked delivery-errors B--E against the node and source text: no new statement-only node carries a proof, no new or duplicate definition is introduced, every non-elementary input is a cited statement, and no citation is to material merely inside another proof. Every proof step is below 2000 characters. citations.json contains the full verbatim statement for each citation, including the exact clauses used. The proof is marked agent-origin because its finite-component calculation fills the blueprint's erroneous infinite quasi-affine shorthand; the final theorem is the locally available Stacks result.

## Mathlib searches and existing-node searches

All five new Mathlib searches in the item were made with msearch.py and are logged in searches.jsonl; all services answered. I tried two different LeanFinder phrasings before concluding no full match. LeanSearch returned generic property descent, quasi-affine facts and finite-affine-open refinements. Loogle returned no hits. The grep found the finite-affine-coproduct calculation in Limits.lean but no ind-quasi-affine scheme-effectivity theorem. I read the returned types and the finite coproduct instance; none proves all item clauses in one specialization. The item's inherited Q42 searches are retained unchanged.

DAG searches for 0APK, 0AP6, ind-quasi-affine, finite affine coproducts and their keywords found the existing general effectivity theorem and the existing finite-coproduct/affine-qcqs leaves. Whole-blueprint searches with blueprint_refs.py for quasi-affine, coproduct, 0APK and labelled coproduct found no blueprint node stating this entire item. blueprint_refs.py ancestor confirms det-lem-stratified-lattice-scheme, whose precise proof place remains recorded. No new ids are proposed, so no same-tag pairs require a Not duplicates entry.


## Repair of the returned delivery cc0ffa508f5

The return dated 2026-10-22 09:23 UTC reports that the reader approved the mathematics but the landing encountered a side-project completion that had not been promoted into the live DAG. I continued the retained delivered node and report rather than treating that side completion as a finished live item. The initial required dry run completed successfully at 668de692466. I then compared the retained item with the current shared read clone: the statement, statement dependencies, source and blueprint ancestry agree, while the current live node is unsplit with empty proof and proof dependencies. The retained copy supplies the four proof steps and its five logged searches in addition to the four inherited searches. I kept all nine searches and the original results, citations and review text; no search was invented or rerun.

I rebuilt the sandbox item from the current node's metadata and retained the worker-owned split fields. I re-read all twelve distinct current statement/proof dependencies, not just the quotes: none is merged, and all ten step/node quotes remain verbatim in their current statements. In particular the coproduct node still gives arbitrary disjoint open components, affine-morphism-permanence clause (4) still covers finite affine coproducts, affine-scheme-qcqs still gives quasi-compactness and the intersection criterion, and the current ind-quasi-affine effectivity statement still accepts an arbitrary singleton fpqc cover and imposes no finiteness on the scheme being descended. Thus no dependency needs replacement on this rebase.

I adjusted step 3 to spell out that K and D' are quasi-compact open subschemes of the same affine D, before invoking the current intersection clause. This verifies the actual hypothesis and does not assume arbitrary open restriction preserves quasi-compactness. Step 4 retains the exact substitution A=V, B=X, and scheme V=T into the current general theorem. I re-read the local Stacks 0AP6 definition and alternative criterion and 0APK statement, and the current blueprint proof (2), confirming the same corrected ind-quasi-affine route. The empty and infinite-label cases in the signed review above remain valid. The initial attachment search was repeated against the current project Lean source: the affine-flat and invariant-open descent declarations supply only the partial results already discussed above. No current declaration was found stating the whole item. Every proof step remains below 2000 characters and no new supporting claim needs a node.

The required delivery command rebuilds the commit on the freshly fetched origin/sheaf-dag and preserves the maintainer-owned fields. The final dry run and push after these repairs are the validation and delivery of this repaired artifact; a dry run alone is not a landing or promotion. Promotion of the side completion remains the maintainer's responsibility, as the return says.

The final preflight initially rejected the wording "the item's" in the revised step 3 under its self-containment gate (B2). I replaced it with the full explicit quasi-affine-scheme convention; the mathematical assertion and all citations are unchanged.
