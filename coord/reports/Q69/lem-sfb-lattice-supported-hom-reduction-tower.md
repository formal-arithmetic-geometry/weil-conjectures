# Q69 stage-1 delivery: lem-sfb-lattice-supported-hom-reduction-tower

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-lattice-supported-hom-reduction-tower.json`: the existing item, now split into ten steps. Its statement and statement dependencies are unchanged. No new node, no Mathlib leaf.
- `citations.json`: one verbatim statement extract per cited node per numbered step.
- `report.md`: this report. `searches.jsonl` was produced by the mandated search tool. `write_split.py` is a sandbox-only drafting script, not a project tool.

## Attachments

None. I searched the current project under `lean/WeilConjectures/` for the exact blueprint tag and for supported Hom, reductions, Roos and lattice/completeness notions. There is no declaration giving all clauses of this item. The integral lattice and closed-immersion-stage declarations found concern other statements or different completed coefficient models; they do not attach this ordinary unbounded pulled-back-coefficient statement.

## WANTED

None. The current blueprint, the Stacks source, and Bhatt–Scholze are available in the read clone.

## What was wrong and what changed

The seeded item had a statement but no proof. Its inherited Mathlib searches and all other metadata were retained; actual Q69 search records were appended, without claiming any unrun query. I read both semantic query result sets, LeanSearch, Loogle and the grep output. The results concern generic derived categories, profinite limits, local cohomology, tensor morphisms, and unrelated adic algebra. None states this item or gives a one-line specialization. The second semantic phrasing also gave no match. No new node is needed: the DAG already has each substantive tool.

The blueprint's informal sentence that extension by zero preserves limits must be used with its quasi-compact-open hypothesis (Stacks 09BP); closed direct image exactness likewise uses the retrocompact complement (09BM). Step 1 derives these hypotheses from the actual finite-type-over-a-field setting. There is no statement dispute or change of route. In particular I did not infer constructibility or assume a completed-category equivalence in this item. Its conclusions are in the ordinary unbounded categories of modules over the pulled-back continuous coefficient rings.

The proof retains the unit's Lattices and Integral targets route: free quotient resolutions, target completion, closed support and finite-free tensor, global sections, supported Hom. The parent node's subsequent Milnor upper-bound calculation is outside this item's statement and is not duplicated. The item is not its unit's key node, so no unit record was edited.

## Not duplicates

No new nodes. Searches of the whole DAG and `tools/blueprint_refs.py search` for supported integral lattice, finite free resolution, and derived limits of sequences led to existing tools, which are cited instead. The item's nearest blueprint ancestor remains `det-uniform-constructible-ext-integral`, as reported by `blueprint_refs.py ancestor`; its existing precise `from.place` is retained and `same_as` is empty because no imported node states this full comparison in another form.

## Review by Q69

I read the chapter and unit records and the current `main-20261015` proof, specifically the Lattices and Integral targets paragraphs. I also read the actual Stacks statements and proofs at 09BP (proetale.tex, `lemma-j-shriek-limits`), 09BM (`lemma-closed-immersion-complement-retrocompact-exact`), 0D6K (sites-cohomology.tex, `lemma-RGamma-commutes-with-Rlim`), 04ZA (topology.tex, `lemma-Noetherian-quasi-compact`), and 0038 (categories.tex, `lemma-adjoint-exact`). For the surjective tower I read Bhatt–Scholze, PDF pages 17–18, Propositions 3.1.9–3.1.10 and 3.2.3. I read the coefficient comparison and support-stratum source statements in the current blueprint, the closed-support-ii statement, the affine Noetherian blueprint proof, and the source location 09C3 to which the existing completed-coefficient free-resolution node points. That last node is used for its explicit specialized resolution statement, not by falsely claiming that Stacks 09C3 itself is literally the same statement. No new-node sources are needed.

For C4 I opened and read the statement of every node in `proof_deps`, and for C1 I compared each step with those statements. The step-by-step checks were:

1. `def-weil-finite-type-morphism` supplies the finite affine cover. `lem-wf-affine-noetherian-components` supplies the descending-chain condition on each affine. The maximum of finitely many stabilization indices proves it on the whole space. `lem-sfb-noetherian-space-compact-subsets` supplies compactness of all the inverse-image open subsets. This checks the finiteness hypotheses rather than assuming them. This assembly is elementary from the three cited statements.
2. `def-sfb-lisse-coefficient-module` gives precisely local finite freeness, including locally varying rank and rank zero. On a finite basis the dual has the dual basis and evaluation/coevaluation identities are explicit. Thus the support-Hom finite locally projective hypothesis and the limit lemma's finite locally free dual hypothesis both hold.
3. `sk-prop-sfb-qlbar-colimit-x` supplies the integral coefficient limit with actual quotient projections. `lem-sf-completed-coefficient-free-resolution` supplies the two-term K-flat resolution for that completed coefficient. Its specialization is legitimate after this ring identification. With the lisse definition, a finite direct sum on a trivializing slice computes the reduction and proves injectivity and quotient identification; no assumption that a torsion object is flat is used.
4. `def-pur-localized-ringed-site` supplies the sectionwise slice restriction. Limits of sheaves are evaluated sectionwise; finite sums of modules are finite products. The same coefficient limit on each trivializing slice therefore proves the canonical sheaf completion map for M_0. This is the written local calculation, not an unstated general completeness-descent theorem, and does not exchange a stalk with an infinite product.
5. `lem-weil-pbc-proetale-ringed-open-closed` says exactly that open extension and closed direct image are exact for a quasi-compact complement. `sk-prop-sfb-cartesian-coefficients` supplies the correct inverse-image ring identifications. The pushforward and open-extension definitions identify the underlying sheaf and its induced scalar action, so restriction from A_n to R uses the very same sheaf with the quotient action. Applying exact functors to the displayed short exact sequence proves the quotient sequence for N. The free-resolution node computes the derived reduction. I wrote the chain map between the n+1 and n resolutions: pi in degree -1, identity in degree 0, inducing the usual quotient on cokernels. This proves compatibility, rather than leaving the word 'compatible' unsupported.
6. `det-sf-open-closed-extension-zero-limits` explicitly supplies products for module extension by zero, not just for abelian sheaves of an unspecified coefficient category. Exactness gives kernels. The module adjunction and `lem-weil-pbc-right-adjoint-preserves-limits` supply limits for the closed image. Kernel of 1-shift then proves the needed sheaf-limit preservation of their composite. The limit is the one with the actual quotient projections of step 4.
7. `lem-weil-proetale-surjective-tower-derived-limit` supplies both the derived product identification and the distinguished Roos triangle for a surjective sheaf tower over any ring sheaf. Surjectivity follows from exact quotient sequences and was verified in step 6. `sk-def-pe-derived-completion` then gives exactly the meaning of derived complete, since step 5 identified this tower with N's derived reductions. No merely abstract isomorphism is substituted for the completion map.
8. `sk-lem-formal-closed-support-ii` explicitly supplies both factors' preservation of sequential derived limits, interpreted in its statement as applying the functor to a Roos triangle. L_0 dual is finite locally free by step 2. I checked its coefficient admissibility and open/closed hypotheses. The coordinate equation for 1-shift shows that the image triangle uses precisely the quotient-induced F_n transitions.
9. `lem-kun-site-rgamma-derived-limit` is for arbitrary small ringed sites and unbounded module derived categories, not only ringed spaces or bounded objects. Its statement supplies actual products through sections of the projection maps and the image Roos triangle. Here the site has the final object S, the size convention is in the item, and the target forgets the coefficient action to D(Ab). Reindexing a positive tower as n=m+1 does not change its products or triangle.
10. `det-lem-formal-closed-support-stratum-hom` explicitly states all three derived-Hom identifications, equality of termwise and derived dual tensor, naturality in the target, and the shifted-Hom formula for every integer q. Thus its statement supplies both the derived and cohomological conclusions at N and N_n. Its complementary-open quasi-compactness was checked in step 1 and its source finite locally projective hypothesis in step 2. This avoids citing a definition of global sections for an unproved derived-Hom theorem.

I tested the proof on empty strata, empty X, rank-zero L_0 or M_0, open and closed identity immersions, n=1, all positive n including ramified uniformizers, locally varying finite rank, and negative q. In the identity case it reduces to the usual finite-free dual tensor and quotient tower; for rank zero all terms are zero and their Roos triangles remain distinguished. No finite bound on cohomological dimension or constructibility of intermediate support cohomology is used. I verified the placement of the free resolution in degrees -1,0, so the quotient triangle has N as its unshifted cokernel when multiplication is injective.

I checked delivery-errors B–E point by point: no new-node form errors; no relabelled clauses; no missing non-elementary lemma; every C4 citation has a verbatim extract in citations.json; no reference to the proof of another node for extra data; no scalar-category replacement; no SGA citation. Each non-elementary step is under 2000 characters. The four elementary steps carry only explicit finite-basis, finite-cover or local quotient calculations after the cited facts. I checked the union of uses against proof_deps. The server dry run remains the required independent mechanical validation.

## Tool uses outside the unit

The item's `split_report.tool_uses` explains the generic coefficient, affine Noetherian, compactness, free-resolution, open/closed exactness, categorical-limit, surjective-tower, ringed-site sections, and explicit support-Hom tools. These implement the prescribed unit argument; no theorem of another unit replaces its route. I did not set top-level `tool_uses` or edit the unit/chapter.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled. Maintainer review and subsequent formalization are separate stages.
