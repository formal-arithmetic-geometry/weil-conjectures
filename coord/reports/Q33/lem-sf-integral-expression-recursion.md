# Stage-1 report: lem-sf-integral-expression-recursion

## Files written

- dag/nodes/sec-six-functors/lem-sf-integral-expression-recursion.json: existing statement item, split into eleven steps; not a Mathlib leaf.
- citations.json: thirty verbatim statement quotations for all step citations.
- report.md: this report.

No new nodes, no Mathlib leaves, no unit-file changes, and no Lean changes.

## Attachments

None. Searches by the blueprint identifier and by expression-tree, expression realization and counit substitution in lean/WeilConjectures found no declaration stating the item. The integral-stage and tower declarations found by broader concept searches do not assert this typed-tree recursion and prescribed compactification comparison.

## WANTED

None. The proof is explicitly agent-written: the available blueprint identifies the coefficient-comparison obligation but does not give this induction.

## Corrections and source audit

The statement is unchanged. Its invertibility and domain-preservation assertions are hypotheses, not conclusions imported from a reconstruction theorem. The proof does not use any structural-generator coherence or the parent realization theorem, which depends on this item. It does not infer equality of derived morphisms from finite evaluations.

The source read for the item is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md, especially the sentence about coefficient comparisons preserving reassociation, evaluation and adjunction maps. I also read the chapter record and sk-thm-sf-compatibility unit: the item realizes the coefficient clause below that unit and does not change its route. The current source explains why the extracted obligation is agent-formulated rather than a theorem stated verbatim in the blueprint.

## Searches and duplicates

There are no new nodes to duplicate. I searched the full DAG for expression-tree, expression tree, counit substitution, realization and the direct compactification formula. blueprint_refs.py ancestor identifies fix-prop-coherence, and blueprint_refs.py search expression-tree found no imported node stating this item. The contextual-intertwining node assumes the recursive comparisons and coefficient equation; it cannot prove the present item without circularity. The parent compactification-system-realization explicitly uses this item. The comparison-bridge node is a different composite-compactification theorem and likewise depends on the parent. Neither is used.

All new Mathlib queries were run through the prescribed msearch.py command and their exact logged queries and results appended to the inherited search records. LeanSearch returned adjunction-to-equivalence and counit lemmas; LeanFinder returned adjointification and W-type recursion facts. The second phrasing returned multivariate functor recursion, rather than a typed categorical operation comparison. Loogle returned basic adjunction structures. The grep search for expression/counit/normalized-system combinations found no match; a second targeted grep located toEquivalence and adjointify triangle identities. I read Mathlib/CategoryTheory/Adjunction/Basic.lean around line 676 and CategoryTheory/Equivalence.lean around line 338. They do not state the operation comparisons or the prescribed integral compactification identification. The search results support no Mathlib attachment for the item.

## Tool uses

lem-weil-ringed-tower-pushforward-limit-comparison supplies the canonical proper direct-image/strict-limit comparison, including its projection normalization, as a generic tool. lem-sf-compact-support-restriction-of-scalars supplies the actual quotient transition comparison and composition under successive coefficient homomorphisms. Both are declared in split_report.tool_uses; their use identifies the prescribed maps rather than replacing the unit's route.

## Review by Q33

I read delivery-errors.md B through E, including its repeated imported copy, against the actual node statements. There are no new definitions or auxiliary statements and no hidden existence assertions. Each of the eleven steps is below 2000 characters. The formal calculations remain in the item's proof instead of being relabeled as new lemmas.

Step 1 reads the expression-domain definition, operation-package definition and primitive-realization statement. The first retains full input-family functors and all intermediate bounds; the second supplies actual simultaneous functors; the third supplies natural primitive isomorphisms. I checked the domain-preservation and invertibility hypotheses at each subtree. The only additional fact is that a functor preserves inverse equations, which the step proves. Naturality of inverse maps is obtained by multiplying the given naturality equation by its inverse components.

Step 2 uses the actual reduction/limit adjunction of lem-coef-derived-system-evaluation-calculus. Its statement explicitly supplies a natural counit and triangle identities in derived system categories. Applying counit naturality to A(e_M) gives the displayed unary substitution. The primitive reduction identity used here is an explicit hypothesis of the item; it is not silently attributed to the primitive-realization theorem.

Step 3 applies the same counit naturality to the single binary arrow B(e_M,e_N), using the stated simultaneous tensor operation and primitive tensor comparison. Bifunctoriality is written out. There is no reassociation, symmetry or structural-generator claim in the calculation.

Step 4 sets up the finite-tree induction with a strictly decreasing size. It uses only the allowed expression constructors, primitive natural comparisons, and invertible unit assumed on the complete input domain. Both children of a binary vertex are strictly smaller even when the same variable occurs twice. Step 5 checks the leaf coefficient equation with the actual adjunction triangle identity. Steps 6 and 7 explicitly substitute the two induction hypotheses and the primitive naturality equations to obtain the unary and binary coefficient equations. The arrows have the source and target of the claimed whole-system equation; no componentwise lifting is involved.

Step 8 derives a useful expression for the unary recursion by naturality of d_A and the already proved coefficient equation. At a leaf r_K=1, so c_AK=d_A(K). This is what fixes the open comparison at the specified r_j, rather than an arbitrary isomorphism.

For step 9 I opened lem-weil-ringed-tower-pushforward-limit-comparison and read its entire statement: its comparison is induced by the common underived direct image and commutes with all tower projections. I read its source, Stacks Tag 0A07, sites-cohomology.tex, lemma-Rf-commutes-with-Rlim, first proof using the square of tower topoi, and checked the tag against tags/tags. I also read Tag 0D6E, lemma-derived-pushforward-composition. The strict underlying towers and ringed topoi here satisfy the tool's hypotheses; it needs no finite Tor or boundedness restriction. The extra bounds remain those of this item's primitive comparisons. The proper primitive d_S is the defining-tower comparison in lem-sf-integral-basic-realization, giving the displayed normalization with the actual inverse unit.

Step 10 expands the recursive map for S_p J_j and uses naturality of that canonical comparison. I read the compact-support definition verbatim: the integral functor is the total limit of the fixed compactification's finite direct-image/open-extension tower. Under its canonical identification with Rp_* j_!, the composite Rp_*d_j followed by the inverse direct-image/limit comparison is exactly that defining-tower identification. Thus the direct and recursive comparisons refer to the same prescribed construction. This argument identifies canonical comparisons of derived composites; it does not use agreement on projections as a faithfulness criterion.

Step 11 reads lem-sf-compact-support-restriction-of-scalars, whose statement gives both the direct-image/open-extension coefficient comparison and its composition for successive homomorphisms. It spells out the transition for every m>=n>=1 and compares it with the primitive d_c statement and compact-support definition. The formulas use the same r_j and proper tower throughout. citations.json quotes these actual statements verbatim; no quotation comes from a proof or from a source pointer in lieu of the statement.

I tested leaf expressions, a single unary operation, tensor with two occurrences of one variable, an identity open, an empty open, a zero input, and equal-index quotient transitions. The leaf coefficient identity is the triangle identity; single-operation comparisons reduce to the prescribed d_A; repetition merely repeats an input projection; identity quotients introduce no new maps. The compactification calculation does not require detecting equality by evaluated morphisms. I found no statement dispute, no missing hypothesis used in these calculations, and no reason to alter the statement.

## Unfinished work

No part of this one-level split remains unfinished. The cited unsplit primitive and operation results remain separate project obligations; they are not claimed proved here.

## Resumed dry-run repair

The server preflight rejected the phrase “the item's domain hypotheses” in step 9 under its standalone-node rule B2. I replaced it with the explicit assumption that $H$ belongs to the complete integral input domain and that the actual unit $u_H$ is invertible there. This changes no statement or comparison. On resumption I compared the saved node with the current repository, reread the cited statements, checked all thirty verbatim quotations, and confirmed that no exact project declaration supplies an attachment. The inherited proof, source citations and logged Mathlib searches are retained.
