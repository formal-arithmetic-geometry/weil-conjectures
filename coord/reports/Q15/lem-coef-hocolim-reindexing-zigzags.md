# Worker report: lem-coef-hocolim-reindexing-zigzags

## Files written

- dag/nodes/sec-six-functors/lem-coef-hocolim-reindexing-zigzags.json: statement, repaired split; no whole-item Mathlib match. No new nodes and no new Mathlib leaves.
- citations.json: verbatim statements for every citation in all nine proof steps.
- searches.jsonl: actual additional searches of the hidden localization arguments. All previous searches embedded in the item are preserved; no absent log has been fabricated.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag and for hocolim/homotopy-colimit notions returned no declaration stating the item. The Lean audit and any Lean record are unchanged. No Lean files were written and no compiler, Lake or build tool was used.

## WANTED

WANTED: Daniel Dugger, Combinatorial model categories have presentations, Appendix A, Remark A.3 and Proposition A.4 p.199, proof and Remark A.5 p.200, for the item. Read online by streaming the PDF through pdftotext; no literature file written.

WANTED: Denis-Charles Cisinski, Higher Categories and Homotopical Algebra, Theorem 1.6.6, Corollary 1.6.8 and Remark 7.1.6, pp.24-25 and 325, for the existing coherent-to-ordinary localization foundation. I read the localization section pp.323-325 online. Proof origin remains agent; these are missing archives, not missing mathematics.

## Repair of the return

The sandbox initially contained only .brief markers, with no node, report or search log. The current shared item retained the returned 2863-character Step 1 and the earlier review. I copied that current baseline and retained its statement, statement dependencies, Lean audit, blueprint ancestry, prior Mathlib searches and six later arguments. The repair changes the proof: it replaces Step 1 by three short cited steps, not an unchanged repush or merely a line-break change. Later steps retain their arguments and have their references increased by two (references to the old ordinary-localization setup now point to Step 3). The PDF read also corrected the top-level source pagination and the source of the inverse calculation: A.3/A.4 are on p.199 and the A.4 proof/A.5 on p.200.

The hidden arguments are already stated in lem-coef-localization-homotopy-category, which gives the ordinary localization including natural transformations and the equivalence-edge/isomorphism criterion. The strict comparison uses the complete functor/natural-transformation universal property in the existing Mathlib leaf lem-weil-pbc-localization-universal-property. Thus the return is repaired by citing existing nodes, as its instruction explicitly permits. Creating copies of them would violate the duplicate rule. The nerve/prism correspondence is now inside the cited theorem, not an uncited inline claim. No statement was disputed or changed.

## Not duplicates

No new node. I searched all DAG statements, the whole blueprint via blueprint_refs.py for homotopy category and localization universal, and the Lean source before considering new nodes. The existing lem-coef-localization-homotopy-category covers the coherent-to-ordinary passage; lem-coef-homotopy-category-nerve-adjunction covers the earlier path/nerve presentation; lem-weil-pbc-localization-universal-property covers lifting and equality of natural transformations. I read all three statements and did not create redundant nodes. Additional Mathlib searches were run with msearch.py and inspected: NerveAdjunction supplies the expected adjunction and product comparison, while Localization.Equivalence/Predicate supply ordinary categorical uniqueness tools. Those findings support reuse, not a claim that Mathlib proves the whole reindexing theorem.

## Review by Q15

I read delivery-errors B-E completely and checked the repaired node against the source and every cited statement. For the item I read Dugger Appendix A online: A.3(i) is invariance, (ii)-(iii) reindexing and composition, (iv) the natural-transformation triangle, A.4 the two-composite argument, and A.5 the zigzag extension. The proof keeps that route, using the same coherent localization/projective presentation as the returned version. The blueprint ancestor's paragraph 2 and the chapter/unit records were read; this repair changes no geometric route or unit record. There are no new nodes whose sources need review.

Step 1 takes exactly projective model structures and the actual coherent colimit cocone from lem-coef-model-colimit-localization-comparison. Its hypotheses hold: M is combinatorial, I is small, and functorial projective replacement is the one in the unchanged statement. Step 2 takes precisely ordinary localization with its natural transformations and the equivalence-edge criterion from lem-coef-localization-homotopy-category. The universal property required there is supplied by Step 1. Weak equivalences are a wide subcategory (identities and composition follow from the model axioms); the larger universe contains M. This avoids both size mismatch and confusing an ordinary nerve with its localization.

Step 3 uses that ordinary-localization conclusion and the full localization universal property in lem-weil-pbc-localization-universal-property. I checked its statement includes lifting functors, lifting natural transformations uniquely, and lifting natural isomorphisms. These are exactly what produces Psi, the two lifted inverse isomorphisms, and the equivalence Phi. The strict defining property of the chosen L produces Phi L = gamma. No assertion that gamma is strictly initial is made: the explicit comparison carries invertibility to strict L before saturation.

Step 4 (old Step 2) takes actual localized colimit cocones from the model-colimit node, componentwise equivalence and the dual cocone criterion from lem-cbc-enhanced-functor-cone-calculus, and saturation for arbitrary endpoints from lem-coef-model-localization-detects-weak-equivalences. No cofibrancy of V is assumed. Step 5 (old Step 3) uses the same coherent colimit cocones and the cocone mapping-space criterion for the contractible lifting space; composition and naturality follow by restricting the same coherent cocone, not just its components. Step 6 (old Step 4) uses the definition of coherent transformation in def-cbc-enhanced-diagrams-cones and the cone-calculus criterion. I checked the prism mixed arrow and the direction g_* = gprime_* H(V(a)). Each cited node really states the fact used; citations.json copies its statement verbatim.

Step 7 is the explicit finite induction along both stipulated zigzags; it uses preceding steps and the two different value diagrams V and Vg correctly. Step 8 is the elementary inverse calculation: vu and wv are invertible, l = (wv)^(-1)w and r = u(vu)^(-1) are respectively left and right inverses of v, and l = r. The two g-comparisons are not identified. Step 9 cites saturation with the strict L from Step 3, so the actual comparison is a weak equivalence without endpoint fibrancy/cofibrancy. The natural-isomorphism and strict-identity special cases follow under the same hypotheses.

I checked small cases: empty indexing categories (functors both ways force both empty), a zero-link zigzag, natural-isomorphism zigzags, and I=[1], J a point with g selecting 0, where the arrow V(0) -> V(1) must be a weak equivalence for the natural zigzag to qualify. These tests support the stated value-diagram hypotheses and rule out a nerve-contractibility shortcut. I traversed the dependencies of the reused localization theorem and nerve-adjunction leaf: neither reaches this item, so the repair introduces no cycle. No SGA source is used. The existing generic cone-calculus tool use is retained; the ordinary localization node is in the same unit and the additional universal-property citation is an existing Mathlib leaf, hence no new off-route tool declaration is needed.

All nine proof steps are below 2000 characters, including every non-elementary step (maximum 1109). Statement equality against the read-only baseline is checked directly; the six later proof arguments are preserved apart from their numbered cross-references. No new unsplit node disguises an item clause, no unproved construction data were introduced, and no search was invented.

## Unfinished work

None in the requested stage-1 repair. The existing cited nodes retain their own independent stage-1/stage-2 status; this delivery does not claim to prove Lean.
