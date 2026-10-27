# Stage-1 delivery: lem-trf-double-derived-hom-lower-bound

Group Q82, 2026-10-22. Direct delivery, reviewed by the worker as instructed.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-double-derived-hom-lower-bound.json`: statement node, now split into six steps. Statement, statement dependencies and inherited blueprint ancestry are preserved. No exact Mathlib match for the whole item.
- `citations.json`: seven verbatim statement excerpts, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses the existing Mathlib leaves for bounded-below injectives being K-injective and the standard t-structure's representative equivalence. It also reuses the existing ringed-site derived internal Hom, its resolution-independence lemma, the product Hom complex and derived cohomology.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for double derived Hom, doubleHom, doubleDerived, bounded injective and finiteInjectiveEvaluation. No project declaration states all clauses. General internal-Hom constructions and abstract double-dual discussions do not supply this statement. No Lean was written and no compiler, Lake or build command was run.

## Sources and route

I read `literature/stacks-project/more-algebra.tex`, Tag 0A69, `lemma-internal-hom-evaluate-isomorphism-technical`, including its truncation triangle, the two displayed tail objects and its last sentence. The assigned item makes the second tail's bound explicit. Its degree calculation is expanded here rather than hidden in a new node. I also read `derived.tex`, Tag 070J (`lemma-bounded-below-injectives-K-injective`), Tag 08J5 (`remark-truncation-distinguished-triangle`), and `sites-cohomology.tex`, Tags 0A8X (`section-hom-complexes`), 0A95 (`lemma-RHom-well-defined`) and 08J7 (`section-internal-hom`).

The chapter is sec-trace-formula and the inherited unit is sk-i-curve-zero. I read both records and the current main-20261015 ancestor text for lem-trf-local-term-locality. This is a generic algebraic support calculation below the inherited nearby-cycle/relative-duality branch, not a replacement of a chapter or unit step. The full inherited `blueprint.from` chain is retained; `same_as` remains empty. Blueprint searches for “double derived”, “Hom support” and “0A69” yielded no equivalent imported node. Searches in all `dag/nodes/` for 0A69, double-Hom and bounded-injective/K-injective and truncation statements identified the existing inputs used here. The sibling evaluation-model, signed-shift and connective-comparison nodes concern different assertions and are not needed.

## Mathlib searches

The item had earlier search records, which are retained. I ran the required search command for this item with two LeanFinder phrasings, Loogle, grep and LeanSearch; all five current queries/results are recorded from `searches.jsonl`. LeanSearch reported a rate-limit service failure and is marked unavailable. Loogle returned no hits. LeanFinder returned standard t-structure, Ext-to-single-injective and K-injectivity declarations, not the iterated internal-Hom model and both support bounds. Grep returned thirteen hits in Double, Embedding, TStructure, Factorizations, Plus and Ext infrastructure. Ext vanishing into a single injective is not this arbitrary iterated Hom-complex calculation.

I read Mathlib `Algebra/Homology/HomotopyCategory/KInjective.lean:133` (`CochainComplex.isKInjective_of_injective`) and `Algebra/Homology/DerivedCategory/TStructure.lean:34,90` (`DerivedCategory.TStructure.t`, `DerivedCategory.isGE_iff`). They confirm the two existing leaves, including the strict termwise support of a chosen representative. There is no need to create either leaf again.

## Not duplicates

No new nodes. The two elementary support implications are proof steps, not auxiliary nodes. None of the item's clauses has been moved into a newly named lemma.

## Review by Q82

I checked B–E of delivery-errors against the node statements and the source text. There are no new statements to review, and the existing item statement is correct as written. It assumes bounded complexes of injectives, not merely bounded cohomology, so the use of K-injectivity has its required termwise hypotheses. The one-object site has the trivial topology; modules, products and internal Hom there are ordinary R-modules, products and R-linear Hom. No etale or nontrivial-site stalk comparison is assumed.

Step 1 uses the actual equivalence in `def-sbc-standard-tstructure-derived-category`: cohomological vanishing below q gives an isomorphic complex zero below q. This is not inferred just from a definition of a t-structure: the node explicitly asserts the equivalence, and Mathlib's `isGE_iff` constructs the lower-truncated representative. Thus the quantification over B is not vacuous.

Step 2 uses `lem-weil-pbc-bounded-below-injectives-kinjective`, whose statement applies to every abelian category and every bounded-below, termwise injective complex. Boundedness of J supplies some lower bound a; I has lower bound v by hypothesis. I verified that no upper bound is mistaken for a lower bound. Neither the source B nor the intermediate C needs to be injective. This is Stacks 070J; I corrected a tentative source reference from 070I (the characterization of K-injectivity) to the exact bounded-below lemma 070J before delivery.

Step 3 cites `def-pur-derived-internal-hom` for its explicit permission to use any K-injective representative and its derived bifunctor, and `lem-pur-rhom-well-defined` for the comparison theorem on quasi-isomorphisms. Both statements were opened and read. The first application uses B,J, the second C,I, and the first derived isomorphism is passed through the contravariant first variable with the appropriate inverse. It proves derived-category isomorphisms, not merely per-degree cohomology identifications, and does not assert that C is K-injective or bounded below. The comparison lemma is declared in split_report.tool_uses as a generic tool from another unit; it does not alter the geometric route. No top-level tool_uses field was added.

Step 4 takes exactly the product formula from `def-pur-hom-complex`. For each p, either p<q gives zero source, or p>=q and s>u-q give p+s>u and zero target. The product of these zero modules has one element, so the vanishing is an elementary calculation; no convergence, interchange of infinite products, or exactness of products is used.

Step 5 uses the same opened definition with source C and target I. For each s, either s>u-q gives zero source by Step 4, or s<=u-q and t<q+v-u imply s+t<v and zero target. This is only integer arithmetic and the formula; it does not assume finite generation, projectivity, a Noetherian ring, or exactness of products. Keeping these two short calculations as steps avoids the elementary-node and clause-restatement errors D1/D2.

Step 6 uses the kernel/image definition of cohomology and its factorization through localization, both explicitly stated in `def-weil-abstract-derived-category`. If D^t=0 then its cohomology in that degree is zero; functoriality carries this through the derived isomorphism of Step 3. The constants u,v were fixed before choosing E and q; the calculation introduces no new bound dependent on B, so the uniformity clause follows.

I tested strict inequalities and endpoint cases with a field R=k: take B=k concentrated in degree q, J=k concentrated in degree u and I=k concentrated in degree v. Then C is nonzero exactly in degree u-q and D exactly in degree q+v-u. Thus the bounds have the right signs and endpoints, and cannot be replaced by non-strict inequalities. Taking q=3,u=-2,v=5 puts C at -5 and D at 10, confirming the signs with negative indices. Cases E=0, J=0, I=0 and R the zero ring all give zero derived Hom; an acyclic nonzero representative B still satisfies the termwise estimates whenever it has the required lower support. The proof is uniform for unbounded-above B. No step exceeds 2000 characters; the longest is 824. Every non-elementary input is an existing cited statement, and citations.json quotes it literally.

## Errors, corrections and unfinished work

No STATEMENT-DISPUTED issue: no statement or definition was changed. The imported empty proof is replaced by the explicit support argument. No auxiliary node is required, no attachment is claimed, and no document is WANTED. There is no unfinished mathematical step or omitted sorry; this is stage 1 only.

## Validation

The server review_split passed and the delivery dry run returned OK (not pushed), preflight passed. All writes are confined to this sandbox, and all checks of check_dag/review_split/preflight are run through the server tools as required.

Server review_split: PASS, 0 new nodes. The first delivery dry run rejected two citation excerpts for being shorter than its 40-character minimum. Both were verbatim but too short to expose the hypotheses; I replaced them with the complete statements of the K-injectivity lemma and resolution-independence lemma. No mathematical step or statement changed.

After the citation-excerpt repair, deliver.py --no-push exited 0 with OK (not pushed), preflight passed. The delivery contains the original statement and no new nodes.
