# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-segal-inverse-evaluation.json`: statement node, split into six steps; no Mathlib match.
- `citations.json`: one exact statement quotation for each of the thirteen step/node citations.

There are **0 new nodes and 0 Mathlib leaves**. The two never-delivered draft files `lem-coef-segal-inner-horn-mapping.json` and `lem-coef-segal-coherent-inverse-data.json` have been removed from this sandbox. They were not existing repository nodes. The existing item has been copied afresh from the shared repository so that its original `created` metadata, source, statement, chapter, unit and ancestry are retained.

## Attachments

None. Searches in `WeilConjectures/` of slopmaster2 for the exact blueprint id, Segal/segal, Rezk, WalkingIso, coherentIso and coherent inverse terminology found no declaration. The item has no declaration in `dag/lean_names_upstream.json`. The master checkout was also searched as reference material; it supplies no finished attachment. No Lean was written or compiled.

## Wanted literature

WANTED: Charles Rezk, *A model for the homotopy theory of homotopy theory*, arXiv:math/9811037, Theorem 6.2 and Sections 2.3–2.5, 4, 5.5, 5.7 and 11, for `lem-coef-segal-inverse-evaluation`. I read the online HTML at https://arxiv.org/html/math/9811037, including the proof through Proposition 11.1 and Lemmas 11.6, 11.10 and 11.11. It is not archived in `literature/`, so I did not download it or label this a document-origin proof. The node records an agent-written comparison of the existing DAG classifier with the space-valued formulation. No Stacks tag states Rezk's evaluation theorem.

The elementary latching calculation uses Stacks Tag 017R, `lemma-splitting-simplicial-sets`, whose statement and proof I read at `literature/stacks-project/simplicial.tex:1795–1816`. Its existing DAG node supplies the unique nondegenerate decomposition.

## What was wrong and corrected

The prior sandbox attempted to make the main conclusion into a new lemma about contractible coherent inverse choices. That is a restatement, not a smaller input. Its other new node was used for an unspecified inner-horn filtration of the walking-isomorphism nerve; no such filtration was exhibited. Rezk's actual proof uses an alternating-word filtration and restriction on invertible components along *outer* horns, so the recorded justification was inadequate. I discarded both drafts.

The whole-DAG search found the already existing `lem-coef-segal-equivalence-classifier`, which states Rezk's Theorem 6.2 for Reedy fibrant simplicial spaces, including the actual edge restriction and both endpoint maps. It is reused rather than recreated. The only distinction needing proof is that the item starts in `Fun(Δ^op,S)` and takes derived mapping spaces. Steps 1–3 explicitly establish the model hypotheses and mapping-space identifications; steps 4–6 apply that existing result and identify its map, naturality and endpoint fibers. The statement has not changed and no statement dispute is asserted.

I also restored the original immutable provenance: the earlier draft incorrectly changed `created.item` and `created.group`. The item's original blueprint ancestry is preserved, its proof location is made explicit, and `same_as` is empty after the blueprint searches below.

## Not duplicates

No new nodes are proposed. Searches of the whole DAG for Segal, walking isomorphism, Rezk, inverse data, outer horn, and the relevant model-comparison descriptions found the existing classifier and model lemmas. `tools/blueprint_refs.py search 'Segal'`, `search 'walking isomorphism'` and `search 'equivalence classifier'` returned no blueprint nodes with the same statement. `ancestor lem-coef-segal-inverse-evaluation` returned `prop-coef-integral-exceptional-adjoint`, which is the retained ancestor. The six-functors chapter, the item's unit `sk-prop-sf-biduality-general`, and the current ancestor proof paragraph 2 were read; this generic model-comparison tool serves the inherited enriched derived-adjunction route and does not replace a geometric unit step.

The classifier is an existing, unsplit node in the same unit, not a new leaf or an attachment. Its proof is not borrowed. A read-only traversal of the complete statement/proof dependency closures of the classifier and all model inputs found no path back to this item. The source comparison is therefore not circular even though the two evaluation formulations are close.

## Mathlib searches

I ran the following fresh searches through the prescribed `msearch.py Q34 lem-coef-segal-inverse-evaluation` command and preserved their exact query text and returned records in the item:

- leanfinder: `For a Segal space evaluation of the mapping space from the walking isomorphism identifies the subspace of invertible arrows`.
- loogle: `SSet.StrictSegal.spineEquiv, CategoryTheory.Nerve.isStrictSegal`.
- grep in `AlgebraicTopology`: `SegalSpace|coherentIso|Rezk|walking.?iso`.
- leansearch: `For a homotopy Segal space the nerve of the walking isomorphism represents invertible arrows`.
- leanfinder, second phrasing: `Rezk walking equivalence evaluation theorem for simplicial diagrams of spaces with homotopy Segal maps`.

All services were available. Loogle returned no hits. The semantic hits give strict Segal simplicial sets or ordinary-category nerves. The grep found `CoherentIso.lean` and `NerveCodiscrete.lean`; I read the former's definitions and ordinary functor/isomorphism equivalence at lines 16–129, and the strict Segal definitions at `StrictSegal.lean:39–59`. An ordinary bijection `WalkingIso.equiv` is not a derived mapping-space theorem for a simplicial diagram of spaces. No hit states this item. The inherited searches are retained, and no unrun search is recorded as a fresh search.

## Review by Q34

I compared the item, hypothesis by hypothesis, with Rezk's online Theorem 6.2: its interval is the discrete nerve of the two-object groupoid with one arrow in each ordered direction, evaluation is the arrow `0→1`, and the target is the union of the homotopy-invertible components. Rezk requires a Reedy fibrant Segal model, whereas the item's Segal object is intrinsically space-valued. I checked this distinction rather than silently adding Reedy fibrancy or completeness to the item. The existing classifier says exactly the model version needed; it also states explicitly that the equivalence is over the two endpoint spaces. No new auxiliary statement requires a separate source or edge-case audit.

For step 1 I opened the complete statements of `lem-coef-reedy-model-structure`, `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`, and `lem-coef-simplicial-presheaf-projective-model`. The first supplies the latching and matching formulas and their trivial variants, the second gives unique degeneracy presentations, and the third says that the Cartesian Kan model is simplicial. Unique presentations identify the latching colimit with the degenerate union in each inner degree. A face section recovers the preimage of a degenerate simplex, so intersections with a simplicial subset introduce no new latching relations. This proves the stated relative-latching inclusion; it is not an uncited assertion of general Reedy cofibrancy. The relative-latching pushout-product formula reduces the simplicial model axiom to the cited Cartesian Kan axiom. The nondegenerate-decomposition node is in another unit; it is declared in `split_report.tool_uses` solely as this general combinatorial tool, since no current-unit statement supplies it.

For step 2 I opened `lem-coef-simplicial-presheaf-localization-comparison`, the Reedy theorem, and `lem-coef-kan-quillen-right-proper`. The first explicitly identifies objectwise localization with the full space-valued presheaf infinity category, retaining mapping spaces. It applies to the small category Δ, with universe enlargement allowed by the existing conventions. Reedy replacement is objectwise a weak equivalence by the second node, not a Rezk equivalence or a completion. Matching degree one is `V_0²`, so endpoint projections are Kan fibrations and strict products compute homotopy products by the third node. This verifies every hypothesis of the Reedy Segal classifier.

For step 3 I read the full statement of `lem-coef-simplicial-model-nerve-localization`, together with the presheaf comparison and the classifier's explicit internal-hom convention. The localization theorem requires both cofibrant source and fibrant target; those were established in steps 1 and 2. It identifies enriched maps with coherent localized maps and respects composition. I wrote the evaluation-at-identity and restriction formulas for `F(n)` instead of citing a fully faithful Yoneda theorem that would not state the required mapping-space equivalence. Precomposition makes both vertex maps and the distinguished edge commute, so the comparison identifies the actual evaluation map.

For step 4 the classifier's statement explicitly supplies the edge-induced equivalence and its endpoint maps; its ordinary groupoid is exactly the item's J. This is the only substantial Segal evaluation theorem invoked. It already exists in the DAG, and I introduce no renamed copy. The online proof was checked to ensure that completeness is not among its hypotheses.

For step 5 the presheaf comparison and simplicial localization statements supply coherent transformations and composition compatibility, and the classifier supplies naturality. I verified the target identification by the two inverse equations in the homotopy category: degree-two composition and the degeneracy identity map are preserved and reflected under the model presentation. Thus the target transported is precisely `W_inv`, and the equivalence remains over `W_0²`. Step 6 is elementary: pulling an inverse and its homotopies back gives an inverse on homotopy fibers; the definition of `W_inv` then selects exactly the invertible components. It uses earlier steps and the definitions in the item, not an extra theorem about inverse data.

Small cases checked include the empty Segal object (all relevant spaces empty), the terminal one-object object, a discrete nerve of a category with a noninvertible arrow (the arrow is excluded), and a groupoid nerve (all arrows are included). A nontrivial one-object group shows why no completeness assumption can be inferred: its discrete object space need not equal its space of equivalences. More generally the proof retains the entire homotopy mapping spaces rather than passing to components before evaluating. Empty latching degree zero and the fact that E has arbitrarily high simplices cause no finiteness restriction: Reedy replacement is for the small category Δ, and no finite-skeletal inverse limit is used.

Against delivery-errors B–E, there are no new statement-only nodes to be self-contained or searched separately; every non-elementary input is an existing statement opened above. Each use has an exact quotation in `citations.json`. No source proof or definition is treated as a statement of an unavailable theorem. The only off-unit citation is explicitly declared as a generic tool. No SGA source, new Lean file, compiler, live-project mutation, or new hypothesis is used.

## Unfinished work

None within this one-level split. Existing dependencies retain their own statuses and are not edited. The fresh second reader should review the comparison steps and then deliver; this worker runs only the required dry run.

## Second reading by Q34

- Item statement: checked against Rezk, *A model for the homotopy theory of homotopy theory*, §§5.5, 5.7, Theorem 6.2 (arXiv:math/9811037); the two-object groupoid, edge restriction, invertible-component target, endpoint fibers, and absence of completeness all agree, including empty, terminal, discrete non-groupoid, and groupoid cases.
- Step 1: checked each use against the full statements of `lem-coef-reedy-model-structure`, `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`, and `lem-coef-simplicial-presheaf-projective-model`; the latching calculation and pushout-product argument are the stated Reedy and Cartesian model arguments, with no omitted non-elementary citation.
- Step 2: checked against `lem-coef-simplicial-presheaf-localization-comparison`, `lem-coef-reedy-model-structure`, and `lem-coef-kan-quillen-right-proper`; objectwise Reedy replacement, matching fibrations, and homotopy fiber-product identification supply exactly the classifier hypotheses, with no completeness added.
- Step 3: checked against `lem-coef-simplicial-model-nerve-localization`, the presheaf comparison, and the classifier's internal-hom definition; representable evaluation and all restriction maps are explicitly identified, and the cited statements provide the derived mapping-space comparison.
- Step 4: checked against the complete statement of `lem-coef-segal-equivalence-classifier`; its `I[1]`, discrete nerve, distinguished edge, endpoint maps, and equivalence onto the equivalence components match the item's `J`, `E`, and `W_inv`.
- Step 5: checked transport of degree zero/one, endpoint maps, composition, identities, naturality, and the actual edge restriction against the classifier, presheaf localization comparison, and simplicial localization statements; the cited nodes state the required mapping-space and composition compatibilities.
- Step 6: checked as an elementary pullback-of-equivalence argument using the item's definitions of homotopy fibers and invertible components; no extra node is needed.
- New nodes: none. The whole-DAG search found the existing `lem-coef-segal-equivalence-classifier`; the two discarded drafts were restatements or unsupported filtrations and remain absent. The cross-unit input `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` was checked against Mathlib `Degenerate.lean:114,217,225,233` and Stacks Tag 017R, label `lemma-splitting-simplicial-sets`; it is already a Mathlib leaf, so its redundant `split_report.tool_uses` request was removed. The classifier is now split in the shared DAG; its earlier unsplit status in the first review has no bearing on its use as a cited statement.
- Changes: removed the redundant tool-use exemption request for an existing Mathlib leaf; retained the mathematical proof and all thirteen verbatim citation quotations. Appended the fresh LeanFinder query `homotopy fiber of evaluation from the nerve of the walking isomorphism in a Segal space` and grep query `Rezk|SegalSpace|homotopy.?invertib|WalkingIso` with their actual returned records; the hits concern strict Segal sets or ordinary WalkingIso functors, not this derived theorem. No Lean, compiler, build, live-project, or SGA-4 material was used.
