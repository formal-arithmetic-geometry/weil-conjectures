# Q08: lem-sfb-compactification-middle-over-base

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-compactification-middle-over-base.json: existing statement, now split into five steps, with the statement unchanged. No new nodes and no new Mathlib leaves.
- citations.json: seven entries, one for every step/node citation, copied verbatim from the cited statements.
- searches.jsonl: actual msearch.py queries and results recorded by the search command.
- report.md: this report and self-review.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and for compactifications and their relative structure. Compactification/Over.lean supplies AlgebraicGeometry.Compactification.overZ, isOver_g, isOver_i, locallyOfFiniteType_over, quasiCompact_over, isSeparated_over (lines 48–68), and overObj/overI/overG and their properties (109–150). These implement substantial parts, but do not state uniqueness among all structure morphisms or absolute quasi-compactness of Z under the item's hypotheses. Thus these declarations do not give every clause, and I did not claim ATTACH. HasCompactification.of_isOver (Compactification/NagataCompactification.lean:255) is an existence assertion with assumptions on X; it is not this item. compactificationOverField is a choice, also not this item.

## WANTED

None. All literature used is present locally.

## Corrections and scope

The imported item is true as stated; no STATEMENT-DISPUTED correction is needed. Its proof was empty. I retained its source, blueprint ancestry, hypotheses and conclusion. I supplied the explicit base-compatibility and uniqueness equations, then the two composition applications and absolute quasi-compactness. Quasi-separatedness of S is unnecessary for this particular argument but remains in the statement. No assumption on a_X, no density of i, and no existence or choice of a compactification is added.

I read the current main-20261015 unit and chapter records, and the unit's _section.md. The unit's recorded argument composes proper p with the separated finite-type structure morphism of Y; the split follows that argument. It does not invoke Nagata to choose another compactification. The blueprint searches for compactification, middle scheme, 01KU, and structure morphism together with compactification found no other blueprint node stating this complete extracted item. same_as stays empty.

## Existing results reused / Not duplicates

No nodes were created. I read the full statements of def-weil-scheme-over-base, sk-def-nagata-sketch-data, def-weil-proper-morphism, def-weil-finite-type-morphism, lem-weil-pbc-proper-fp-permanence, lem-sfb-finite-type-composition-base-change and lem-weil-pbc-qcqs-morphism-permanence. The last three are existing Mathlib leaves. No off-route non-leaf tool is needed: sk-def-nagata-sketch-data is in the unit's route, and the other reused nodes are definitions or Mathlib leaves.

## Searches

The inherited item's Mathlib search records are preserved. New searches were run exclusively with the required msearch.py command and appended to the item. LeanFinder was tried with both the complete geometric conclusion and a second phrasing emphasizing the slice-category factorization. Loogle found IsSeparated.instCompScheme and related permanence lemmas. The grep found Scheme.Hom.isOver_iff at Mathlib/AlgebraicGeometry/Over.lean:49, with no Mathlib Compactification declaration. LeanSearch returned general lifting and factorization declarations. The second LeanFinder phrasing found MorphismProperty.HasFactorization.over and Scheme.Hom.asOver/isOver_iff; the former assumes a global factorization property and does not assert this item's uniqueness and geometric/absolute compactness clauses for the given c. No single exact declaration or one-line specialization covers the full item. The needed general results already have DAG leaves, so no search result requires a new node.

I also read Mathlib's separated composition instance (Morphisms/Separated.lean:75), locallyOfFiniteType_comp (FiniteType.lean:68), quasiCompact_comp (QuasiCompact.lean:69), and QuasiCompact.compactSpace_of_compactSpace (QuasiCompact.lean:150), confirming the existing leaf interfaces used here. I did not run a compiler or change Lean.

## Review by Q08

For the item I read the main-20261015 sk-def-sfb-dc-setting statement and the unit's recorded proof, which explain exactly the composite structure map and the closure of Z under the separated finite-type setting. For the detailed geometric facts I opened Stacks schemes.tex, Tag 01KU (lemma-separated-permanence, composition); morphisms.tex, Tag 01W1 (definition-proper), Tag 01T1 (definition-finite-type), and Tag 01T3 (lemma-composition-finite-type); and schemes.tex, Tag 01K4 (lemma-quasi-compact-affine). Their tags were checked against tags/tags. This is an agent-written expansion of the blueprint argument, recorded as such, not a claimed verbatim documentary proof. There are no new nodes needing separate source review.

Step 1 uses the statement of def-weil-scheme-over-base, which actually defines S-morphisms by the structure-map equation and the category Sch/S. sk-def-nagata-sketch-data actually supplies the factorization and the open/proper properties. I wrote a_Z i = a_Y (p i) = a_Y f = a_X and observed that the condition on p alone forces any other structure map b to equal a_Y p. The slice equation is equality of those same underlying maps. This is elementary, rather than a separate lemma, and it does not use a density condition on i.

Step 2 uses only def-weil-proper-morphism: its statement explicitly includes both separatedness and finite type in properness. It is a direct extraction of these two hypotheses from the assumed proper p, so is elementary. It does not treat the definition as a theorem about stability.

Step 3 cites clause (e) of lem-weil-pbc-proper-fp-permanence. I checked that this clause states composition of separated morphisms, not merely separated base change or proper composition. I substitute p:Z→Y and a_Y:Y→S. Both hypotheses are available, and the composite is the map constructed in step 1.

Step 4 cites clause (1) of lem-sfb-finite-type-composition-base-change. This explicitly states finite-type composition, including quasi-compactness, so there is no hidden use of a locally-finite-type result as a finite-type result. Its two hypotheses are step 2 for p and the item's hypothesis for a_Y.

Step 5 cites def-weil-finite-type-morphism only to extract quasi-compactness of a_Z. It then cites the quasi-compact half of clause (2) of lem-weil-pbc-qcqs-morphism-permanence, whose statement explicitly says a quasi-compact morphism to a quasi-compact scheme has quasi-compact source. I checked its substitution U=Z, T=S and both hypotheses. This is the absolute scheme conclusion, not a repetition that a_Z is quasi-compact. A finite affine cover of S has quasi-compact inverse images by 01K4 and covers Z, explaining the topological content of this application.

Against delivery-errors B–E: all statement notions are either defined inline or cite the existing definition nodes; statements of every cited node were read, and citations.json copies their words rather than a proof or a definition's unstated consequence. The two elementary steps contain their arguments. The three non-elementary steps each cite the exact existing result. No step creates an object using mere existence, changes coefficient layers, cites SGA, changes the unit route, or hides a comparison or existence argument. No new node restates a clause, and no new node is elementary or duplicates an existing result. No proof step is longer than 2000 characters.

I checked the empty case X=∅: uniqueness still follows from the required compatibility of p, even if i has empty image. If Z=∅, all the same equations and permanence applications apply. For p=id_Y the construction reduces to a_Z=a_Y and recovers the assumed properties of Y. Extra proper components of Z disjoint from X do not affect the uniqueness argument, which uses p rather than i. Neither S nor Y is assumed Noetherian or affine in any step. The use of quasi-compactness of S is essential for the last conclusion: with S=Y=Z an infinite disjoint union of spectra of a field and p=a_Y=id, all the relative identity properties hold but Z is not quasi-compact. This verifies that the argument uses the actual base hypothesis rather than assuming a field base silently.

## Unfinished work

None in this one-level split. All proof dependencies already exist; no further statement-only nodes were needed. Delivery validation is recorded below when it completes.

## Validation

The required deliver.py --no-push invocation exited successfully: OK (not pushed), commit d4e469602fa, preflight passed. The final delivery invocation will validate and push the packaged split.
