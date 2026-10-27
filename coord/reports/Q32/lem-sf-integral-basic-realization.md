# Stage-1 report: lem-sf-integral-basic-realization

## Files written

- dag/nodes/sec-six-functors/lem-sf-integral-basic-realization.json: statement item, split into five steps; not in Mathlib. Statement and statement dependencies preserved verbatim. Existing creation provenance retained.
- citations.json: 24 entries, one for each step/node citation, checked against the current node statements.
- report.md: this report. searches.jsonl contains the five searches performed for this item; prepare.py is a sandbox-only preparation script.

No new nodes, no new Mathlib leaves, no unit edits, no Lean writes or compilation.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by integral realization, semilinear systems, strict towers and Roos terminology. The existing normalized-tower and adic realization modules do not state this simultaneous primitive package with all four operations, the specified open unit formula and the compact-support coefficient transitions. Nothing is proposed as an attachment.

## WANTED

None. The source PDFs and Stacks sources used here are present locally.

## What needed repair

The imported item was statement-only. Its principal risk was replacing a comparison of whole derived strict towers by a list of finite-level isomorphisms. The proof now constructs pullback and tensor on simultaneous quotient representatives, fixes the normalized Roos comparison, invokes its natural descent for arbitrary derived morphisms, and records the actual proper-image and compact-support transitions. The open comparison is the existing specified r_j and actual completion unit, with their adjunction normalization.

The blueprint sentence in fix-prop-coherence.proof.md lists coefficient-compatible generators but does not prove this extracted obligation. Accordingly proof_origin.by is agent. Stacks 0941 and Zheng 4.10 are cited only for their literal limit/evaluation results; the stronger whole-system and naturality refinements are cited as existing DAG lemmas, not attributed verbatim to those sources. No expression-tree coherence, reconstruction theorem, proper-base-change assertion or new invertibility claim is inserted.

## Searches and reuse

Read the inherited Mathlib search summaries in the item, then ran five searches through msearch.py with this item's own group/item pair. Both LeanFinder phrasings return ordinary adic-completion or sheaf right-Kan-extension lemmas, not derived coefficient-system realization. Read AdicCompletion.ofTensorProduct_naturality at Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean:74: it concerns ordinary module adic completion and cannot specialize to the item. LeanSearch returns ordinary inverse-system equivalences, sheaf pullback and existence of limits. Read SheafOfModules.hasLimit and hasLimitsOfShape in Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean:68 and :82; these do not supply the derived strict-tower comparison. Loogle likewise returns presheaf colimit instances, and the source grep's sole hit concerns semilinear typeclass inference. None is a match. Every newly recorded query is exactly in searches.jsonl with its actual result; no service was reported unavailable by these calls.

Searched the full DAG and blueprint with semilinear, Roos, integral realization and quotient tower terminology, and inspected the ancestor of the item (fix-prop-coherence). Reused lem-pur-quotient-system-flat-models, lem-pur-flat-roos-functor-descent and lem-weil-strict-roos-comparison instead of adding parallel model or descent lemmas. The full statement of lem-pur-completed-primitive-counit-comparison was also read, but its extra normalized-counit clause is unnecessary here. No blueprint node states this entire primitive package; same_as stays empty.

## Not duplicates

No new nodes were created. The existing quotient-model, Roos-descent, open-reduction and scalar-restriction nodes are cited directly.

## Review by Q32

I read the current item, its statement dependencies, the six-functors chapter record, sk-thm-sf-compatibility and its single collecting step, and the source fix-prop-coherence.proof.md. The item realizes only the primitive-operation part of its coefficient-generator sentence. I also read Stacks sites-cohomology.tex Tags 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat), 0941 (lemma-derived-limit-is-ok), 0D6E (lemma-derived-pushforward-composition), and 0GL1 (lemma-j-shriek-and-tensor), checking tag/label pairs against tags/tags. I read Bhatt--Scholze Definition 3.4.10, Lemma 3.4.12 and Lemmas 6.5.8--6.5.9, and Zheng Construction 4.1 and Lemma 4.10 (4.10.1). The blueprint definitions of derived direct image and integral compact support were read alongside their current DAG statements, whose transition paragraphs make explicit what the old blueprint leaves implicit. No new node requires an additional source.

Step 1 uses lem-pc-kflat-resolution for flat-term K-flat representatives, lem-coef-derived-system-evaluation-calculus for the actual reduction functor, and lem-pur-quotient-system-flat-models for simultaneous pullback/tensor representatives, their transitions and quasi-isomorphism invariance. I checked that the last node states precisely these whole-system formulas, including naturality for cochain maps. The ringed sites are small as required in the item. The calculation for the two tensor transitions is written out, and does not assume the nonflat quotient A_m to A_n is flat.

Step 2 uses lem-weil-proetale-countable-products-exact for the exact-product hypothesis, lem-weil-strict-roos-comparison for the normalized natural comparison with total limit, and the integral operation definition and well-definedness lemma to identify the prescribed quotient-complex functors. The quotient-model lemma supplies invariance required by lem-pur-flat-roos-functor-descent. I checked the latter statement gives naturality on roofs and uniqueness with fixed representative components: it does not infer uniqueness from level projections. The chosen d is the inverse of rho, since the requested arrow runs from total limit to the completed operation. All hypotheses of descent are present (one or two good input categories, exact products, and levelwise quasi-isomorphism invariance).

Step 3 uses the system-operation definition, lem-pur-coefficient-system-derived-comparison and its unbounded comparison node for the simultaneous proper image, not just its evaluated objects. The unbounded comparison explicitly includes representative, scalar-restriction and transition comparisons. I read lem-weil-proetale-direct-image-restriction-of-scalars, including the resolution-map normalization, and matched it with the transition paragraph of def-weil-derived-direct-image. The equality of these specified towers then passes through the total derived limit functor stated by lem-weil-pbc-ringed-strict-tower-homotopy-limit. No inference that evaluation is faithful is used. Properness is retained, although several generic image constructions work for arbitrary scheme maps.

Step 4 uses exactly lem-sf-integral-open-reduction-comparison, which states all the required open claims: r_j is a whole-system natural isomorphism, it preserves the strict quotient maps, j_!K is complete, the actual unit is invertible, and its displayed d_j identifies both open adjunction maps. The derived-system evaluation-calculus node fixes the unit being used. I checked the composition direction: first the inverse of L(r_j), then the inverse of u. Quasi-compactness, invertibility of ell and completeness of K are all in the item's assumptions. This reuses an existing open theorem; no new node merely restates the clause.

Step 5 applies the same simultaneous proper-image comparison to the actual open system. lem-coef-semilinear-derived-sections explicitly supplies exact system open extension and the ordinary open adjunction. I compared the full statement of lem-sf-compact-support-restriction-of-scalars with the desired transition: its comparison is exactly open scalar restriction followed by proper scalar restriction, and it composes for all ring maps A_r to A_m to A_n. Its natural isomorphism is used on the input quotient map before taking the limit. The complete transition paragraph of def-weil-integral-rational-qbar-compact-support uses the same composite and the same chosen compactification. Finally, total Rlim is the functor already cited, and def-sf-integral-system-expression-domain explicitly checks the hidden open intermediate as well as the proper output. Thus the proof does not claim constructibility or uniform bounds from an unproved preservation result: those are the stipulated domain conditions.

I checked small cases: zero inputs give zero comparison towers; identity scheme maps and the full-open immersion reduce to the same quotient complexes and adjunction unit; the empty open has zero extension and zero proper-image tower. For m=n the input quotient and coefficient-restriction maps are identities; for r>=m>=n the quotient maps compose and the cited compact-support scalar comparison has the corresponding cocycle. Tensor signs are unchanged because only degree-zero coefficient transitions are tensored; direct-sum total tensor is retained. No boundedness or Tor interval is enlarged or silently assumed, and no claim is made beyond the expression domain.

I checked B--E of delivery-errors.md against the files: no new node or duplicate, no clause relabelled as a fresh dependency, each cited statement opened and quoted verbatim, no citation of a proof-only construction, no source used as a substitute for a node, and no forbidden SGA source. All five non-elementary steps are under 2000 characters. I checked that none of the proof dependencies reaches the item via statement or proof edges. Off-unit generic tools are declared in split_report.tool_uses with their purpose; no chapter or unit route is replaced. The server check_dag already reports no finding introduced by this sandbox.

## Unfinished work

None in the requested one-level split. The reused unsplit dependencies remain their own stage-1 items.
