# Q66: lem-sfb-polynomial-test-universally-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-test-universally-open.json: item, statement, split into six proof steps; no exact Mathlib match for the item.
- citations.json: 20 entries, one for every (step, cited node), quoting the cited statement verbatim.
- searches.jsonl: actual searches run with the prescribed msearch.py command. Existing item searches are retained; seven searches from this run are appended to its mathlib_searches.
- report.md: this report. prepare_split.py is a sandbox-only preparation helper, outside the delivered DAG.

New nodes: 0. New Mathlib leaves: 0. All prerequisites were found in existing nodes, all of which are already Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, the item id, polynomial/openness combinations, and universal-openness names and prose. No project declaration states this polynomial-test implication. In particular the flat locally finitely presented universal-openness result has extra hypotheses and is not an attachment.

## WANTED

None. The proof and all supporting Stacks sources are present locally.

## Corrections and scope

The item's statement is correct and unchanged, including the absence of finiteness, Noetherian and reducedness assumptions and the quantifier over arbitrary scheme bases. The statement dependencies are unchanged. Previously the item was statement-only. Its source, creation record, chapter, unit and ancestry are preserved. No existing node other than the item is edited, and no Lean or compiler/build command is used.

I read AGENTS.md, the stage-1 brief and stage document, worker role, GOAL.md, the three-level route rules in SETUP.md, the chapter and unit records, current blueprint unit and direct-image proof, and delivery-errors.md B--E in full, including the repeated copy. The item's inherited provenance is an auxiliary algebraic-geometric ingredient of the finite-normal-model openness argument below direct-image stability; this split follows its specified Stacks 0F31 route. It does not replace any chapter or unit argument. This item is not the unit's key statement, so no realized fields are changed. blueprint_refs.py ancestor returns None, matching its existing null from.node. Searches of the entire imported blueprint for universally open, universal openness, polynomial base changes, and relevant tags found no duplicate.

## Not duplicates

No new nodes are proposed. In particular, I reused lem-weil-pbc-base-change-image rather than introducing a second image/base-change lemma; reused lem-weil-pbc-fibre-product-affine-spectra for the affine model; and reused the tensor and polynomial universal-property nodes. The generic-element evaluation and its pushout check are short applications of those universal properties, carried explicitly by the proof steps rather than made into new nodes. No clause of the item is renamed as a prerequisite.

## Review by Q66

I read more-morphisms.tex, Tag 0F31 (lemma-test-universally-open), statement and complete proof at lines 21726--21788. Its algebra paragraph represents one tensor element by finitely many pure tensors, replaces those finitely many base coefficients by variables, and specializes back. My proof gives that argument directly, rather than an unexplained invocation of 0F31. The source's quasi-compactness observation about the open image is unnecessary to the image equality, so I do not introduce a quasi-compactness hypothesis. I also read schemes.tex Tags 01I4/01JQ on affine fibre products, 01IT on affine-open bases, and 01JY on base change of open immersions; morphisms.tex Tags 0495/01S1 including the arbitrary-subset image identity; algebra.tex Tag 00CX including tensor generation and Tag 00E0 for the principal-open basis; and modules.tex Tag 0H78 for inverse images of basic opens. There are no new nodes needing further source checks.

For step 1 I opened lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-spec-localization-away-basic-open. The first states the tensor spectrum isomorphism with both projection formulas for arbitrary commutative algebras, and the second explicitly states the principal-open basis. Here B is any commutative A-algebra, so both apply without a finite-type condition. Switching the two fibre-product factors gives the stated projection b maps to b tensor 1. This identifies the actual base-change map, not only an abstract affine scheme.

For step 2 I opened def-weil-pbc-module-tensor-product, def-weil-pbc-mv-polynomial-ring and lem-weil-pbc-algebra-tensor-pushout-universal-property. Their statements respectively give generation by pure tensors, evaluation and uniqueness for polynomial algebras, and the multiplication and factor-inclusion formulas for tensor algebras. Absorbing each finite module coefficient into b_i gives the displayed finite sum. The evaluation sends h to precisely g by the displayed product calculation; no equality in a residue field is substituted for an equality in the tensor ring. This step is elementary relative to those cited statements.

For step 3 I re-read the exact tensor pushout statement, including its existence and uniqueness clauses, the polynomial universal property, the affine fibre-product model, the spectrum functor and the fibre-product definition. For a compatible u and v, E is an A-algebra via their common restriction; thus the algebra-hom hypotheses of the tensor lemma hold. The resulting w has the required restriction to B and, by checking C and every variable, the required restriction to S. Its formula on b tensor c proves uniqueness. This is a short universal-property verification of the very square needed in step 4, not an unsupported tensor-associativity identification or a new specialized openness lemma. None of the cited statements imposes flatness. I deliberately kept the actual maps k and e in the square to fix its orientation.

For step 4 I opened lem-weil-pbc-basic-open-pullback and lem-weil-pbc-base-change-image, as well as the principal-open basis node. The first gives inverse images of basic opens for any scheme morphism, and k(h)=g from step 2 supplies the correct function. Crucially, the second states q(p^{-1}(C))=g^{-1}(f(C)) for EVERY subset C, not merely preservation of surjectivity. Apply it with C=D(h), p=alpha, q=q_B, f=f_n, g=beta in the cartesian square proved in step 3. This gives exactly the equality used, and continuity of beta then proves openness. No general claim that an open map remains open after arbitrary base change is used; that would be circular here.

For step 5 the same basis node says every open is a union of principal opens. Images commute with unions as a set identity, so step 4 proves openness on all opens. This is the second elementary step and it hides no lemma.

For step 6 I opened lem-weil-pbc-affine-opens-basis, def-weil-affine-spectrum, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-base-change-image, def-weil-open-immersion and def-pc-fibre-product. The first provides an unrestricted affine open cover of T, not a finite cover. The spectrum statement gives the ring map A to B_j for each restricted base morphism. Open-immersion stability makes P_j to P an open immersion, and the subset image formula identifies its range as q^{-1}(W_j); the open-immersion definition then supplies the homeomorphism onto that open. Fibre-product uniqueness gives the displayed reassociation by its pairs-of-maps property. Thus step 5 applies to q_j on the correct inverse-image scheme. The final set equality and union are ordinary topology. No intersection of two affine opens is assumed affine, and T need not be quasi-separated or quasi-compact.

I tested the possible degenerate cases: n=0 gives the coefficient square and the empty finite sum g=h=0; zero rings give empty spectra and empty images; B may have nilpotents and infinitely many algebra generators; C may be zero; T may be empty or admit only an infinite affine cover. The construction and each cited hypothesis still make sense. All other g use only finitely many tensor summands, independently of generation of B or C. I found no statement dispute or source error.

The Mathlib searches used both phrasings of the polynomial-test statement. LeanSearch and Loogle return universal-openness definitions and locality; LeanFinder also returns affine-space projection openness and unrelated base-change stability theorems. I read the universal-openness source; those results do not prove the test implication, and smoothness/finite-presentation assumptions on other hits cannot be obtained from this item. Each new search entry is transcribed from the actual sandbox log; inherited searches were not invented or attributed to this run. Since all prerequisite nodes already exist, no duplicate definition or unchecked Mathlib leaf is created. All proof citations have verbatim statement quotes in citations.json, proof_deps is precisely the union of uses, every step has a source and a Boolean elementary value, and every proof step is shorter than 2000 characters. The two comparisons in steps 3 and 6 are fully written universal-property verifications from the cited statements, with no omitted comparison lemma.

## Unfinished work

None in the requested one-level split. Server dry run and direct delivery are performed after this review; their authoritative results are the delivery tool output.
