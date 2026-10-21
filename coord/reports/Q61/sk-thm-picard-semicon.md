# Q61 stage-1 report: sk-thm-picard-semicon

## Files written

- dag/nodes/sec-picard-framework/sk-thm-picard-semicon.json: statement, split by reuse of the existing reviewed same-unit theorem thm-pc-semicontinuity-base-change; no Mathlib match for the full statement.
- dag/units/sk-thm-picard-semicon.json: only realized and realized_by changed. The item realizes the statement; the existing detailed theorem carries the unit's sole proof paragraph.
- citations.json: exact statement excerpts for the theorem cited in steps 1, 2, and 3.
- report.md: this report. The required msearch.py calls created searches.jsonl; their queries and actual results are recorded in the item.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the project sources for the item id and semicontinuity/cohomology terminology and read Cohomology/DirectImage/Semicontinuity.lean, BaseChangeMap.lean, and the base-change morphism API. AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber (Semicontinuity.lean:92) supplies the semicontinuity clause; AlgebraicGeometry.Scheme.Modules.exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant (line 175) supplies local freeness with locally varying rank. Neither states the canonical base-change isomorphism conclusion. The additional bijective_cechBaseChangeMap_of_forall_specializes in BaseChangeMap.lean:242 assumes a reduced Noetherian affine base, so cannot attach the unrestricted item. No finished declaration of the project was found covering all clauses under the item's hypotheses. This is not a claim that the entire mathematical result has already been proved in Lean.

## WANTED

None. The current blueprint statement and both the sketch proof and expanded theorem proof are available locally.

## What was wrong and what changed

The imported item had one long proof paragraph using only sk-thm-picard-coherence and left its actual linear algebra and canonical-map argument unexposed. However, the DAG already contains the expanded, split-and-reviewed theorem thm-pc-semicontinuity-base-change, in this exact unit, with every conclusion and identical hypotheses. It is more precise, also asserting finite-dimensionality and explaining the necessity of reducedness. Creating new lemmas here would duplicate that existing split. I therefore reused its statement, not unexposed details of its proof. This is reuse of an existing reviewed result, not moving the item's clauses into new nodes.

The imported statement dependencies sk-def-av-jacobian and sk-def-av-pic do not define any notion the statement uses. I replaced them by the existing definitions of scheme base change, morphism properties, higher direct images, module flatness over a base, reduced schemes, finite locally free sheaves with variable rank, and sheaf cohomology. In particular def-pc-finite-locally-free defines a morphism property and is NOT the sheaf notion needed here: the correct node is def-sc-finite-locally-free-sheaf. I left the item statement, import flags and all other maintainer fields unchanged. The item blueprint.same_as now records the expanded theorem.

No statement dispute was found. The theorem is about structure-sheaf modules and Zariski sheaf cohomology; no etale or pro-etale coefficient category is substituted. No SGA source is used. No off-unit proof tool is used.

## Mathlib and duplicate searches

I ran the required logged msearch.py LeanFinder, Loogle, LeanSearch, and grep commands. The first Loogle pattern contained the unrecognized identifier AlgebraicGeometry; it is recorded as unavailable, not as proof of absence. I followed it with the valid UpperSemicontinuous name query. The two different natural-language LeanFinder phrasings returned flat-morphism facts, rankAtStalk, and unrelated module/condensed-sheaf declarations, not the theorem. LeanSearch returned algebraic flatness and rank facts. The targeted AlgebraicGeometry grep found no result. A second grep found Module.isLocallyConstant_rankAtStalk in FreeLocus.lean:224, its free-locus variant at line 186, and Module.free_of_flat_of_finrank_eq in LocalRing/Module.lean:422. I read these: they assume module flatness already and do not provide cohomology-and-base-change for a proper family. Loogle's UpperSemicontinuous results are definitions and generic topology properties, not this theorem. No hit states the whole item or specializes to it in one line.

The whole-blueprint search for semicontinuity returned this item, the existing expanded theorem, and an unrelated boundary semicontinuity lemma. The Grauert search returned no further blueprint node. I read the existing theorem's actual statement, review note, proof, and blueprint_update; its updated statement adds only the expected local rank assertion, and still entails this item. There are no new-node duplicate pairs to justify.

## Not duplicates

No new nodes. The existing thm-pc-semicontinuity-base-change is deliberately reused, and blueprint.same_as names it. No new clause nodes, elementary nodes, or Mathlib nodes are created.

## Review by Q61

I read the current main-20261015 chapter and unit sketch, sk-thm-picard-semicon/_section.md, sk-thm-picard-semicon.proof.md, and thm-pc-semicontinuity-base-change.md plus its proof in the same directory. I also read the full DAG theorem statement and its current-blueprint update. The detailed theorem implements precisely the unit's finite-free model, rank-minor semicontinuity, and reduced-base normal-form route. The theorem is in the same unit as the item; taking its reviewed statement as a lemma preserves that route and adds no alternate proof.

For step 1 I checked the first sentence of the cited theorem: f is proper of finite presentation, F is an O_X-module of finite presentation flat over T, and q is an integer, exactly as in the item. Its first clause explicitly gives a CANONICAL base-change map with source R^q f_* F tensor the same residue field and target the same scheme-theoretic fibre cohomology. I did not infer canonicity from a mere existence of an isomorphism. The source notation R^q f_* F tensor kappa(t) means the sheaf fibre, i.e. its stalk tensor kappa(t); this is the same notation in both statements.

For step 2 I checked the literal clause (2): beta^q is defined as the same dimension function and is upper semicontinuous on the entire base. The step takes exactly that assertion and imposes no new finiteness, smoothness, or Noetherian hypothesis. For step 3 I checked the literal clause (3): reducedness and local constancy, not global constancy, are the only additional assumptions; the conclusion explicitly includes finite local freeness, flatness and isomorphy of the same phi^q(t) at EVERY point. The citations.json quotes are verbatim excerpts of the actual DAG theorem statement for all three steps. No step uses an uncited non-elementary fact, and no step is longer than 2000 characters.

I checked the definition-node statements as well: def-pc-base-change defines the fibres and module pullbacks; def-pc-morphism-conventions supplies proper and finite-presentation morphisms; def-pc-derived-direct-image defines R^q through cohomology and a module in degree zero; def-pc-scheme-module-flat-over is flatness over the base via f; def-pc-reduced-scheme means reduced local rings; def-sc-finite-locally-free-sheaf allows the finite rank to vary between local charts; def-sc-sheaf-cohomology-functor defines H^q. I excluded derived pullback from the statement dependencies because it appears in the expanded theorem's proof, not the item's statement.

For small cases, the empty base has vacuous pointwise assertions and local freeness; the zero sheaf has zero dimensions, zero higher direct images and the unique isomorphism on zero fibres; negative q has zero higher direct image and zero cohomology, consistent with the theorem's integer quantifier. On a disconnected reduced base the ranks may differ on different components, so the variable-rank sheaf definition is essential. Reducedness was retained: the sketch's square-zero elliptic-curve family illustrates why a one-point nonreduced base must not be admitted in clause (3). None of these checks needs a new lemma in this split because the existing theorem states the assertions for all these cases already.

I checked delivery-errors B-E against the final files. B: no new incomplete or non-self-contained nodes, no fabricated searches or source attributions. C: every proof-step dependency is the reviewed theorem and every cited clause is literally in its statement; no use of its proof in place of its statement and no generic off-unit tool. D: no new restatements or hidden arguments were introduced, and the detailed theorem's existing split remains responsible for its route. E: no dropped hypotheses, wrong fibres or replacement of the canonical map by a noncanonical equivalence. The imported sketch's explanatory counterexample is not an extra conclusion of the item, so no independent deformation-theory claim is added here.

## Unfinished

No stage-1 mathematical work remains for this item after successful delivery. This split does not certify the existing theorem's Lean closure or independently re-split its already-reviewed proof. Validation and push are performed with the mandated deliver.py commands.
