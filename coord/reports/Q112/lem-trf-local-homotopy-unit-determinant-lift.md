# Stage-1 delivery: lem-trf-local-homotopy-unit-determinant-lift

## Files written

- dag/nodes/sec-trace-formula/lem-trf-local-homotopy-unit-determinant-lift.json: statement, split into six steps; no Mathlib match for the whole item.
- citations.json: four step/node quotations, checked against the current node statements.
- report.md and the actual search-command log searches.jsonl.

New nodes: 0. New Mathlib leaves: 0. The existing leaf lem-trf-rectangular-determinant-switch is reused.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint id and by homotopic surjections, common-complement names and det_one_add. The only nearby project hit was the use of Matrix.det_one_add_mul_comm in LinearAlgebra/IdempotentCharpolyLocalCharpoly.lean:49; it proves a different characteristic-polynomial calculation.

## WANTED

None.

## Corrections and route

The statement is unchanged. The item had no proof. Stacks more-algebra.tex Tag 0FJK (lemma-homotopic-surjections), first, second and final proof paragraphs, gives the homotopy-lift construction and common-summand strategy. Its surrounding theorem has a quasi-isomorphism hypothesis, which the present auxiliary statement does not have. We do not import that hypothesis or its kernel-acyclicity argument: the inverse of 1+dt is 1-dwt, where w=(1+td)^(-1), and both products are expanded explicitly in step 4. This proves invertibility directly from that of 1+td and works under exactly the item's hypotheses.

Tag 0FJF (lemma-det-switch), statement and rectangular identity, supplies the determinant equality through an existing Mathlib leaf. Its trace-based proof is unnecessary here; the leaf matches Matrix.det_one_add_mul_comm (Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:401-406), whose source I read.

Read the latest blueprint at literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and its .proof.md, together with the DAG chapter and unit. The ancestor now describes contracting-correspondence specialization, rather than explicitly stating this remote local-algebra descendant. The inherited ancestry is retained, with its exact auxiliary determinant-calculus role explained in split_report; no claim that the latest ancestor states the present result is made. Searches of the whole DAG (source tags, common-summand and homotopy notions) and blueprint_refs searches for homotopic and determinant found no blueprint node stating this local lifting assertion. Both non-elementary inputs already exist; no new clauses or special-case nodes are manufactured.

## Not duplicates

No new nodes. Reused lem-trf-local-common-summand-surjections (the simultaneous summand) and lem-trf-rectangular-determinant-switch (the matrix identity). Other nodes at 0FJK concern the field common section, residue lifting, determinant normalization locality/equivariance, or the parent homotopy-invariance calculus. The item proves the explicit chain automorphism and its inverses rather than repeating those results.

## Unfinished

None within this one-level split. Existing downstream unsplit nodes remain their own work items.

## Review by Q112

I read Stacks more-algebra.tex:36420 onward (Tag 0FJF) and :37016 onward (Tag 0FJK), including the final common-summand paragraph and the preceding construction's use of a homotopy. No new node needs a separate source review. I also read all four cited node statements in full: def-weil-pbc-free-module, lem-trf-local-common-summand-surjections, lem-trf-rectangular-determinant-switch, and def-weil-pbc-exterior-algebra. The quotation manifest copies their actual assertions, rather than conclusions found only in their proofs.

Step 1 uses the basis-to-coordinate isomorphism from the free-module definition and the common-summand statement's two restriction isomorphisms and direct-sum conclusion. Finite bases exist by hypothesis, so both coordinate ranks are finite nonnegative integers; localness and both degree-minus-one surjectivities are exactly the summand lemma's assumptions. Its coordinate presentation is transported back by the chosen isomorphisms, not silently treated as a different module.

Step 2 uses only the given homotopy equations, a^{-1}s=1, and the chain-map equation a^0 d_P=d_Q a^{-1}. Expanding both components verifies ak=b and expanding d_P(1+td_P) verifies the chain condition. No homotopy-invariance theorem is being assumed.

Step 3 writes out the block components on N direct-sum U. The term td_P lands in U; applying the injective restriction of a^{-1} identifies the U-block as (a^{-1}|_U)^{-1}(b^{-1}|_U). Both restrictions are isomorphisms, so B is invertible. Ordinary multiplication in both orders verifies the displayed block inverse. N is not assumed finite free and no determinant of its block is taken.

Step 4 is elementary associative algebra, not the source's acyclic-kernel argument. From Kw=wK=1, right-compose each equality with t, yielding the two identities needed to compute LV=VL=1 for V=1-d_Pwt. Multiplying the chain equation by these inverses verifies the inverse chain equation. I checked the order of every composite: t:P^0 to P^{-1}, d_P:P^{-1} to P^0, and w acts on P^{-1}.

Step 5 uses exactly the rectangular identity in lem-trf-rectangular-determinant-switch, with D of size rank(P^0) by rank(P^{-1}) and T of the reverse size. No equality of ranks is needed. This is the only non-elementary determinant identity and is a cited node, already a Mathlib leaf. The current Mathlib searches returned homotopy-category and Dold-Kan results, not the desired chain automorphism; their statements and the matrix hit were read. A second semantic phrasing was tried before recording no match. Prior inherited searches are retained without inventing queries.

Step 6 uses the exterior-algebra definition's multilinearity and alternation and writes out the basis expansion giving the determinant scalar. The generator's coefficient map is the alternating determinant form, showing it is a basis; no uncited freeness theorem is invoked. Exterior powers respect inverse compositions by their action on wedges, so the inverse scalar exists. Precomposition on the dual multiplies by that inverse scalar, and the tensor generator is fixed. These are explicit few-line calculations from the definition, kept as a step rather than a new node.

For the B--E checklist: all objects and notions remain introduced in the unchanged statement; its three statement dependencies are retained. There are no new nodes with hidden proof text, duplicate tags, false leaf claims, or missing searches. Every cited use was checked against its statement (C4); the only non-elementary assertions are cited inputs (C1). No cited input depends on this item and no parent determinant-calculus theorem is used. The proof carries the block and inverse arguments instead of outsourcing clauses of the item. Each step is shorter than 2000 characters.

I tested zero-rank cases: if Q^{-1}=0, then U=s=t=0 and both components are identities; if P^{-1}=0, then Q^{-1}=0 by surjectivity; if P^0=0, then t=0 and both are identities. For zero differential, the two homotopy equations force a=b and K=L=1. For h=0 the same identity construction results. Empty determinants and empty wedges are 1, so the determinant-line argument covers these cases. Finite residue fields, including F_2, require no infinite-field assumption because the existing common-summand statement includes them. The zero ring is excluded by the item's definition of local ring as having exactly one maximal ideal. No statement dispute was found, no hypothesis added, no SGA source used, and no Lean or compiler command run.
