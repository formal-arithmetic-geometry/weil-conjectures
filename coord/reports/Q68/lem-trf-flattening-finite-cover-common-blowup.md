# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-flattening-finite-cover-common-blowup.json: statement, split in six steps; no exact Mathlib match.
- citations.json: verbatim statement quotations for every proof-step citation.
- report.md: this report.

No new nodes and no new Mathlib leaves. The original statement, statement dependencies, source and blueprint ancestry are retained. The searches.jsonl log is retained and its actual searches are appended to mathlib_searches; the pre-existing Q85 searches are preserved. write_split.py is sandbox scratch, not a delivery file.

## Attachments

None for the item. Searches under lean/WeilConjectures for the blueprint id, common blowup, flattening and strict-transform/flat combinations found only partial inputs. The existing product-blowup, flat-blowup-base-change and strict-transform-as-blowup nodes already carry their project attachments. None states the whole finite-cover assertion, so those are used as dependencies rather than claimed as an attachment of this item.

## WANTED

None. All sources used are present in literature/.

## Findings and corrections

The imported item was statement-only. I found no false clause, no missing hypothesis and no need to change its statement. I expanded the first paragraph of Stacks 081R into a proof, using the product centre specified by this item rather than an unspecified dominating modification. In particular, domination alone would not license strict-transform composition: the support equality in step 2 is essential. Surjectivity of a blowup over its centre is neither assumed nor used.

The original blueprint ancestor is lem-trf-local-term-locality through the historical nearby-cycle/alteration auxiliary branch recorded in blueprint.from. The current main-20261015 ancestor has a contracting-correspondence statement, which I read; this delivery does not change that chapter, unit, ancestor, or its route. It splits only the already dispatched auxiliary algebraic-geometric item. The sk-i-curve-zero unit record is not this item's key statement, so its realization fields are not edited.

## Not duplicates

No nodes are created. I searched the whole DAG and blueprint for product blowup, strict transform, the tags 080A/080I/080F/080Y, and source-open restriction. This found existing interfaces sufficient for the entire argument. In particular I reused thm-nagata-blowup-product-ideal rather than creating a two-ideal factorization node, lem-trf-strict-transform-composition rather than another 080I node, and the existing strict-transform-as-blowup plus flat-base-change interfaces rather than creating a special case of 080F. The module-strict-transform calculus is not cited for a theorem about scheme strict transforms.

## Review by Q68

I read flat.tex, Tag 081R (lemma-flat-after-blowing-up), its entire first proof paragraph, and divisors.tex Tags 080A (lemma-blowing-up-two-ideals), 080E (lemma-strict-transform), 080F (lemma-strict-transform-flat), 080I (lemma-strict-transform-composition-blowups), 0805 (lemma-flat-base-change-blowing-up), and 02NS (lemma-blowing-up-projective). I also read morphisms.tex Tag 01R8 (lemma-quasi-compact-scheme-theoretic-image), especially clause (3), and its flatness/finiteness base-change statements, and schemes.tex Tags 01K5, 01KU, 01KV and 03GI behind qcqs permanence. For the current blueprint interfaces I read the main-20261015 product-blowup, strict-transform-as-blowup and flat-base-change node texts. There are no new-node sources to check.

For step 1 I opened the statements of def-nagata-admissible-blowup, thm-nagata-blowup-product-ideal, def-nagata-blowup-product-comparison and thm-nagata-global-blowup-complement. The first is the finite-type-ideal datum actually required, the second and third identify precisely the iterated blowup in the extended second ideal, and the last handles a unit centre. Finite products and extension preserve finite generating lists by the explicitly written generator argument, which is a few-line algebra step rather than a new lemma. No inverse-image flatness is being assumed here.

For step 2 the global-complement node states exactly the isomorphism off V(I_i). Applying it only there proves the missing inclusion of zero sets. The opposite inclusion is immediate from extension and primality; points in V(I_i) are accounted for separately. This verifies the full support hypothesis of the composition node without claiming equality between V(J_i) and the image of its whole inverse image on the centre.

For step 3 I opened all eight cited statements (including the construction nodes defining the comparisons). lem-trf-strict-transform-composition requires an isomorphism with the product-centre blowup AND the support equality; steps 1 and 2 give them. It supplies scheme strict transforms with inclusions and projections, not only modules. thm-nagata-strict-transform-is-blowup identifies the next scheme strict transform with the blowup of the extended ideal. thm-nagata-blowup-flat-base-change and def-nagata-blowup-flat-base-change-map apply because the first strict transform is flat over T_i by hypothesis. Their comparison has the same projections as def-nagata-strict-transform-blowup-comparison; the universal-property node supplies uniqueness of the lift for the same exceptional ideal. Thus the resulting isomorphism has the required inclusion/projection compatibility, not merely an abstract isomorphism. Flat base change of a morphism is exactly the conclusion of lem-weil-pbc-flat-morphism-base-change. The lfp clause is exactly permanence (3). No finite-type assumption on the original g is introduced.

For step 4 I opened def-nagata-strict-transform, def-nagata-scheme-theoretic-closure, lemma-nagata-scheme-image-restrict-open and the permanence node. The image-restriction node assumes a quasi-compact quasi-separated map. I checked that the relevant open immersion is the base change of the complement of a finite-type ideal: finitely many generators on each affine give its quasi-compactness, permanence (3) preserves it, and its diagonal is an isomorphism. Only then is the restriction theorem applied. The restricted closed subschemes are exactly the individual strict transforms in their ambient opens, so they cover the whole transform. I never assume intersections of arbitrary affine opens are affine.

Step 5 uses only the pointwise definitions of flatness and local finite presentation, both of whose statements I read. A point and its neighbourhood may be taken in a covering open, so this is elementary and does not hide a descent theorem.

For step 6 I opened the qcqs permanence, strict-transform-as-blowup, blowup-proper, proper, finite-type and separated-implies-quasi-separated statements. This avoids silently asserting a qcqs composition result which a definition node would not state. First W is qcqs by permanence (2). Its strict transform is a blowup in an extended finite-type ideal and is proper over W, hence quasi-compact and quasi-separated by the cited statements. Permanence (2) gives a qcqs source. Likewise T^b is qcqs. Permanence (1) now applies to the actual final morphism. Local finite presentation plus these two properties is the definition of finite presentation in the cited lfp node. This matches the first sentence of the 081R proof with no density hypothesis.

I checked small cases: a single chart makes J_1 the unit ideal and q_1 the identity; all unit ideals give the original scheme and the local hypotheses already prove the claim; U empty imposes no density condition; zero/nilpotent product centres can have empty blowup and the support argument still works because V(I_i) is included separately; an empty affine cover forces W empty, and the unit product gives T with empty strict transform. Empty charts cause no exception. The proof does not replace scheme-theoretic closure by topological closure. Every non-elementary input is a cited existing statement, with exact quotes in citations.json; no tag is substituted for a node. Proof dependencies are exactly the union of the uses. Every step is under 2000 characters, no new statement duplicates a clause, and no proof contains an SGA citation. All off-unit theorem citations are already Mathlib leaves or audited closed project nodes; the one open composition theorem belongs to this unit, so no new off-route tool declaration is needed.

## Unfinished work

None in this stage-1 item. Required server dry-run and final delivery are performed after this report is written; their success is reported by the delivery command.
