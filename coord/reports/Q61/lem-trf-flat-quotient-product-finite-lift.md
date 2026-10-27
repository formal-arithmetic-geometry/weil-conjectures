## Worker report

Item: lem-trf-flat-quotient-product-finite-lift. Group Q61. Stage 1 only. Direct delivery under the dispatched brief.

### Files written

- dag/nodes/sec-trace-formula/lem-trf-flat-quotient-product-finite-lift.json: split, with three proof steps; statement and statement dependencies unchanged.
- citations.json: one full, verbatim statement quote for each of the two step citations.
- report.md: this report and self-review.
- searches.jsonl: the unmodified results logged by msearch.py for five searches. The six inherited search records in the item were retained, and the five actual Q61 searches appended.

New nodes: 0. New Mathlib leaves: 0. The proof reuses lem-weil-pbc-flat-tensor-exact, an existing Mathlib leaf, and def-weil-pbc-module-tensor-product. The elementary finite-coefficient argument is written in the item instead of creating a node.

### Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, quotient-product terminology and finite-lift/support terminology found no project declaration covering every clause. Mathlib results are not project attachments.

### WANTED

None. All sources used are present in the read-only clone.

### Findings and corrections

The statement is correct, including its absence of surjectivity and Mittag-Leffler assumptions. The source's flat Mittag-Leffler hypothesis is used earlier in Tag 0AS6 to make a different product-of-tensors map injective; this item already assumes vanishing in the tensor of the product. Its kernel calculation and finite refinement require only flatness. I have not altered the statement.

The imported item had no proof. I supplied the coordinate kernel calculation, then cited exact tensoring for an arbitrary exact pair, and explicitly chose the finite generating list and the final tensor. In particular, I did not replace q by a surjection or silently exchange the tensor of a product with a product of tensors.

The inherited blueprint ancestor is lem-trf-local-term-locality. I read its current statement/proof and the current sk-i-curve-zero unit under literature/blueprint/latest. They concern contracting local terms, while this node belongs to the existing long supporting-algebra branch. I retained that provenance and identified the precise Tag 0AS6 sentences this item realizes. No unit or chapter route was edited. Blueprint searches for quotient product, flat Mittag, flat tensor, finite support and tensor did not identify another blueprint node stating this item.

### Unfinished work

None in the mathematical split. Required dry run and delivery follow this report.

## Not duplicates

No new nodes were created. The whole DAG was searched for the source tag 0AS6, flat/exact tensor results, finite tensor support and the relevant Mathlib names. The exactness fact was already lem-weil-pbc-flat-tensor-exact and was reused. The least-support theorem lem-trf-flat-ml-minimal-support is the parent using this item and is not a proof dependency; citing it would be circular. lem-trf-tensor-kernel-factorization concerns factorization of maps with a finitely presented cokernel, not the elementary coordinate kernel or finite tensor coefficients here.

## Review by Q61

I read algebra.tex, Tag 0AS6 (lemma-minimal-contains), from the second displayed map through the final finite-generation paragraph. I also read Tag 00HB (definition-flat) and Tag 00HD (lemma-flat) to verify that the flatness convention used by our definition implies the exact-pair theorem. There are no new nodes whose source or statement needs a separate review.

For Step 1 I checked each equivalence directly: the j-th coordinate of q(e) vanishes exactly when e belongs to N_j, so simultaneous vanishing is membership in K. Linearity follows coordinatewise from quotient operations. This gives exactness at E only and makes no assertion of surjectivity onto P. This is elementary and has no hidden theorem citation.

For Step 2 I opened the statement of lem-weil-pbc-flat-tensor-exact. It explicitly applies to any exact pair N1 -> N2 -> N3 with kernel equal to image, and explicitly concludes exactness after right tensoring by a flat M. Substitute N1=K, N2=E, N3=P, f=i_K, g=q, using Step 1. R is commutative and M is flat as required; neither P flat nor q surjective is required. Exactness yields precisely the displayed image/kernel equality and supplies t. This is the only non-elementary fact in the proof and it is a cited node, not merely a source tag. The existing leaf is verified by Module.Flat.rTensor_exact at Mathlib/RingTheory/Flat/Basic.lean:340, whose arbitrary exact-pair hypotheses I read; I also read lTensor_exact at :323 and ker_lTensor_eq at Flat/Equalizer.lean:35.

For Step 3 I opened def-weil-pbc-module-tensor-product and checked that its statement includes generation by pure tensors, bilinearity, and the induced map formula. These are exactly the clauses used: a finite linear combination of pure tensors becomes a finite sum by absorbing each scalar into the second factor; the images in E of its first factors span L; their membership in K gives L contained in K. The same finite sum with each first factor regarded as an element of L is the desired z. Applying the induced-map formula gives x term by term. No identification of tensor spaces as literal subspaces, no submodule finiteness theorem, and no finite presentation assumption is needed. This is the two-or-three-line finite coefficient argument explicitly exempted from new-node creation by the brief. For comparison I read Submodule.exists_fg_le_eq_rTensor_subtype at Mathlib/RingTheory/TensorProduct/Finite.lean:35 and exists_fg_le_eq_rTensor_inclusion at :58; they verify the same elementary construction but need not generate another DAG node.

I tested J empty: P is the zero module, q is zero, K=E, and the proof simply takes a finite support for any tensor. If M=0 or x=0, the empty sum permits L=0 and z=0. If one N_j is zero, K=0 and flat exactness forces x=0, again giving L=0. With R=E=M=Z and two zero submodules, q is the diagonal Z -> Z x Z and is not surjective; the exact-pair argument still applies. With all N_j=E, q=0 and every tensor has the finite support constructed in Step 3. None of these cases requires M to be Mittag-Leffler.

Against delivery-errors B1-B10: there are no new-node schema, definition, duplicate, source-tag or leaf-record issues to introduce. I preserved the item statement and checked the exact project attachment search; the Mathlib search queries and raw result summaries are exactly those actually logged. All five Q61 searches returned successfully. The first LeanFinder search ended during the launcher pause; its completed log entry and named hits were read on resumption, and their relevant source declarations were opened instead of repeating that search. A second phrasing found flat tensor kernel equivalences, not the complete item. The finite ideal Chinese-remainder candidate is restricted to finite coprime ideals and cannot replace arbitrary submodules indexed by any set.

Against C1-C8: each non-elementary input has the single appropriate statement citation, both cited node statements were read, their full statements were copied into citations.json, and proof_deps is exactly the union of uses. The only off-unit statement is an existing Mathlib leaf, so no new tool-use approval is needed. No citation points back to this item or its parent.

Against D1-D5: the item itself carries the argument and constructs L and z; it is not relabeled as new nodes. There is no induction or omitted standard comparison. All three proof steps are shorter than 2000 characters. Against E1-E7: the modules, factor order, coordinate quotient maps and final tensor domains are explicit, and the above small cases check the only delicate absent hypotheses. No source error or statement dispute was found. My correction was to supply the previously absent proof with these exact hypotheses and explicit formulas. The repository and launcher were only read, and no Lean, compiler, Lake or build command was used.
