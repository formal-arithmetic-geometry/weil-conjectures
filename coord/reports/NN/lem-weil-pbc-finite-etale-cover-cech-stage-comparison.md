# Worker report

Item: lem-weil-pbc-finite-etale-cover-cech-stage-comparison. Group NN. Date 2026-10-21.

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-cover-cech-stage-comparison.json: statement node, split into seven proof steps; Mathlib searches found infrastructure but no declaration giving the full comparison.
- citations.json: a verbatim statement quotation for every step/node citation, including hypotheses and the clause used.
- searches.jsonl: five actual searches made through the required msearch.py command, preserved as logged.
- report.md: this report.

There are zero new nodes and zero new Mathlib leaves. The sandbox initially contained only dispatcher marker files, with no earlier item, report or search log to preserve. The item was copied from the live read clone; inherited searches and all original metadata were retained.

## Attachments

None. The exact blueprint tag has no declaration under lean/WeilConjectures. Searches by Čech, colimit, limit and continuity led to Comparison/Continuity.lean, FiniteEtaleCechFilteredColimit.lean, EtaleLimitFiniteCechComplexColimit.lean and related files. The first proves comparison-section continuity, the second varies coefficients on a fixed étale covering, and the third gives an existential descended covering for étale-site coefficient systems. None states this item's fixed-stage pro-étale comparison and every cohomology clause with its specified legs. In particular, their existence is not evidence for an exact attachment.

## WANTED

None. The proof source is already available locally: literature/stacks-project/proetale.tex, lemma-limit-pullback (Tag 099S) and lemma-affine-vanishing (Tag 099U), especially the second displayed Čech-colimit calculation. I read these sections through the use of injectivity. The split stops before that use. I also read the nearest blueprint ancestor's second-limit paragraph in literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-comparison-injective-acyclicity.md. This ancestor is not present at the analogous main-20261015 path; the item's recorded source/ancestor remains applicable and has no blueprint_update. No SGA source is used.

## Corrections and scope

The imported statement is true as written, and its text and hypotheses have not changed. It was unsplit. Its proof now makes explicit the directed tail, affineness of the limit and nerve objects, finite presentation at stages, the face-compatible inverse-limit identification, the section comparison legs, the differential equation, and the passage to cohomology including degree zero. The unit and chapter route are unchanged: this is precisely the second-limit subargument of the comparison-injective-acyclicity ancestor, not an alternate proof of proper base change. No unit realization fields need editing because this is not the unit's key statement.

During self-review I added the existing affine-limit theorem explicitly: affineness of U and the coordinate-ring colimit description must not be silently assumed just because every stage is affine. I also separated limits of nerve schemes from colimits of section groups; only after the former universal property is checked is the section formula applied.

## Not duplicates

No new nodes. Whole-DAG keyword/tag searches for 099S, 099U, comparison sections, filtered colimits and finite products found the existing section comparison and two algebraic Mathlib leaves. Whole-blueprint searches via blueprint_refs.py for continuity, 099S, Čech and Cech found no blueprint node stating this full comparison in another form. The first-limit Čech comparison is different: its stages need only be ind-étale over X and its coefficients stay M. The item is the second limit, whose stages are genuinely étale over X and whose stage coefficients are F. Neither was duplicated.

## Review by NN

I read the chapter and unit records, the three levels in SETUP.md, GOAL.md, the worker/stage-1 brief, and delivery-errors B–E in full (including the repeated archived version). I checked the following mathematics against the actual cited node statements and the source, rather than taking a declaration name or a proof as an interface.

Step 1 uses only the ordered Čech definition for the empty-family calculation. I wrote the extension of a cone from the directed tail explicitly; it uses common upper bounds, not an unquoted cofinality theorem. Empty products of abelian groups give zero complexes when m=0.

Step 2 uses the affine-limit theorem for U. The étale finite-limit/base-change node supplies precisely the nerve base-change isomorphisms and their étaleness over each base. The affine-scheme morphism node and affine permanence clauses (1)–(3) give affine nerve objects and affine transitions. Covering base change includes joint surjectivity, so every stage family and the limit family still covers. The composition node supplies étaleness over X, the étale definition supplies local finite presentation, and the scheme-conventions definition says finite presentation means that plus quasi-compactness and quasi-separatedness; the last two follow from the cited affine permanence statement. Thus no separatedness or finite-type assumption on X has been added.

Step 3 uses the full fibre-product universal property, which I opened and read. A cone into the base-changed system is exactly one map to the fixed initial nerve and a compatible cone into the U_i. This proves the limit claim directly. Deleting a factor commutes with these identifications because the composites with every retained factor and the base projection agree. Repeated indices remain distinct factors; no argument treats these products as open intersections.

Step 4 uses the affine-limit theorem's explicit Spec(colim) clause and the ind-étale presentation definition to verify the basis-object hypothesis. The existing comparison-sections node states naturally, for module sheaves, M(T)=colim F(T_i) for affine étale finite-presentation stages; it gives exactly the desired section formula. The site-comparison definition specifies the unit, restriction functor, and module inverse image by applying the set inverse image to addition and scalar operations. These justify the stated additive unit-and-restriction legs without changing left-module coefficients, assuming commutativity of Lambda, or assuming injectivity.

Step 5 uses the finite-limits Mathlib leaf, whose statement explicitly includes abelian groups and finite products, together with the Čech definition's product over all ordered tuples. The product index is finite in each degree, even though the complex has infinitely many degrees. There is no interchange of an infinite product with a filtered colimit.

Step 6 uses the natural section comparison and the Čech differential formula. Its displayed equality is the actual restriction identity for each deleted factor followed by the finite alternating sum. I wrote the universal property that makes degreewise colimits into a colimit of complexes, so there is no additional non-elementary lemma hidden behind an unspecified transport. Every check here is a direct universal-property or naturality calculation from already cited statements.

Step 7 uses the same finite-limit leaf for kernels and the filtered-colimit exactness leaf for C_i^(q-1) -> Z_i^q -> H_i^q -> 0. Their hypotheses are met because the tail is small, nonempty and directed, and the objects are abelian groups. The quotient is precisely the definition of Čech cohomology. At q=0 the incoming group is zero, not an augmentation. All maps on kernels and quotients are induced by the original section maps.

For delivery-errors B, no unsplit new statement is introduced and the item keeps its source and blueprint fields. For C, every non-elementary input has a cited existing statement; citations.json quotes those statements verbatim, and no step uses a construction buried only in a cited proof. For D, the argument is carried by the seven item steps, with no replacement node for the item or its clauses. For E, I checked the empty family, empty affine schemes, singleton cover, constant system, zero ring/zero sheaf, q=0 and repeated indices. None requires a point, injectivity, positive-degree vanishing, or a nonzero ring. All proof steps are shorter than 2000 characters; the elementary steps are explicit cone and differential universal-property calculations.

The Mathlib searches were run with the exact query texts recorded in the item and searches.jsonl. LeanSearch and LeanFinder returned general sheaf, affine-limit, finite-product and homology infrastructure; Loogle returned cechComplexFunctor. I read that construction in Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean: it defines a general complex and does not assert this comparison. The grep found no Čech-colimit/pro-étale comparison theorem in CategoryTheory. I retained the inherited records rather than inventing or rerunning them.

## Unfinished work

None in this one-level split. No Lean was written and no compiler, Lake or build command was run. Required server dry-run and delivery results are recorded below after completion.

## Verification

Server review_split passed with zero new nodes. The required deliver.py --no-push invocation then exited successfully: OK (not pushed), commit 1967fe21636, preflight passed. This was the only active delivery invocation. No local maintainer check or compilation was run.
