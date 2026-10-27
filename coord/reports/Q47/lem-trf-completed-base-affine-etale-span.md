# Worker report: lem-trf-completed-base-affine-etale-span

## Files written

- dag/nodes/sec-trace-formula/lem-trf-completed-base-affine-etale-span.json: statement, split into six proof steps; no exact Mathlib match.
- citations.json: verbatim statements for every step/node citation.
- report.md: worker report and direct-delivery self-review.

No new nodes; no Mathlib leaves created. Existing item searches, statement, source, creation record and blueprint provenance retained. Five further real searches are recorded with their actual outputs in the item and searches.jsonl. The sandbox initially contained only dispatcher markers, so there was no previous proof/report to recover.

## Attachments

None. Searched WeilConjectures for the blueprint id, completed-base affine/etale span, completion/isomorphism and common etale neighbourhood concepts. No declaration states this item. Existing completed-affine comparisons concern different constructions; none supplies formal approximation.

## Wanted literature

None.

## Problems found and corrected

The item was statement-only, with no proof. Its statement is valid and unchanged. Its source is Stacks 0GDX's first paragraph, using 0CAV; this also supplies the proper source route for this historical nodal auxiliary branch. The latest blueprint's lem-trf-local-term-locality proof now uses contracting correspondences and contains no nodal approximation paragraph. I read that latest proof and the unit record; I retain the inherited explicit historical provenance and do not claim that the latest proof still contains it or alter the chapter/unit route.

The key omitted details were the scalar-compatible completed-stalk comparison before 0CAV and finite presentation after affine shrinking. I supply both using existing nodes. I also restrict uniqueness of x_B to points over the PAIR (x,b), as the statement correctly does: points over x in other formal fibres are not asserted unique. For finite presentation I explicitly cite affine-morphism permanence for quasi-compactness and quasi-separatedness; local finite presentation alone would not suffice.

## Unfinished work

None for this one-level stage-1 split. The existing cited nodes remain independent proof obligations at their own levels.

## Not duplicates

No new node is created. Reused lem-trf-completed-local-base-change and lem-trf-isomorphism-completion-approximation rather than creating versions of either. Reused the existing complete-local G-ring and Noetherian/local completion nodes as well.

## Review by Q47

I read literature/stacks-project/more-morphisms.tex, lemma-relative-map-approximation-pre (0GDX), especially its first paragraph, and lemma-isomorphism-approximation (0CAV), its full statement and proof. For the algebra setup I read algebra.tex lemma-hathat-finitely-generated (05GG), lemma-radical-completion (05GI), lemma-completion-Noetherian-Noetherian (0316), and more-algebra.tex proposition-Noetherian-complete-G-ring (07PS). I checked the final finite-presentation argument against morphisms.tex definition-finite-presentation (01TP), lemma-noetherian-finite-type-finite-presentation (01TX) and the affine permanence statements. There are no new nodes requiring separate source reviews.

For step 1 I opened the statements of finite-type-over-noetherian, affine-open-locnoeth, affine-open-stalk-localization and localization-noetherian. The first gives precisely Noetherianity over Spec Z, the second applies to S itself, and the last two identify A as a Noetherian localization; none is being used merely for a definition. For step 2 I opened adic-completion-noetherian, local-completion-local-ring, module-completion-complete, complete-local-g-ring and the locally Noetherian definition. The completion's maximal ideal is explicitly m_A C, its residue field comparison is canonical, and powers of that extended ideal coincide with the module filtration. Thus the complete-local G-ring theorem's Noetherian, local and complete hypotheses all hold, rather than assuming that arbitrary completions are complete without finite generation.

For step 3 I opened completed-local-base-change, fibre-product-points and fibre-product-point-residue-field. The first gives the actual C-algebra completed-stalk isomorphism and the point over (x,b), but does not state the residue isomorphism; the two fibre-product statements plus the written tensor-field calculation prove that additional clause. This repairs the potential C4 mistake of taking an unstated residue clause from completed-local-base-change. For step 4 I opened finite-type-composition-base-change and isomorphism-completion-approximation. Both base-changed families are locally finite type over B, both points lie over b, O_(B,b)=C is a G-ring, and theta composed with the inverse of the given formal isomorphism has the orientation of 0CAV and respects base scalars. N=2 is permitted. No exact recovery of the original formal isomorphism is required by this item.

For step 5 I opened pointed-etale-neighbourhood-affine-shrink and etale-composition-cancellation. The shrink lemma applies with Omega=kappa(u) and the canonical point, so it needs no algebraic closure. The open immersion is etale, and composition preserves etaleness for the other leg. Cofinality of neighbourhoods inside an open gives the unchanged stalk and residue field directly. For step 6 I opened the etale and unramified definitions, proper-fp-permanence clause (e), lft-fp-locnoeth, affine-source-morphism-separated, affine-source-separated-target-affine-morphism, and affine-morphism-permanence clause (3). They supply, respectively, local finite type of a, composition with X_B/B, local finite presentation over B, separatedness of the affine target, affineness of H/B, and both remaining global finiteness conditions. No proof of another node is used as its interface. Off-unit non-Mathlib tools are declared in split_report.tool_uses, with their generic foundational role.

I checked delivery-errors B through E: no new statement-only/definition obligations, no restatement nodes, no unexplained tag in place of a dependency, no non-elementary step marked elementary, and every uses entry has a verbatim statement quotation in citations.json. All steps are under 2000 characters. Small cases checked: x need not be closed (the field tensor computation remains valid for arbitrary kappa(x)); A a field (completion and base change are the identity); A Artinian nonreduced (completion is A and locality/completeness still hold); positive-dimensional fibres (no finite residue extension or closedness of x is needed); empty X or Y cannot satisfy the marked-point hypotheses. The local sigma assumption ensures b maps to t; the formal isomorphism is used only after its scalar compatibility has been preserved. No added hypothesis or weakened conclusion is needed.

The server review_split check and the first full deliver.py --no-push preflight passed. Final checking corrected the Properties locally-Noetherian tag to 01OW and wrote out quasi-compactness of the local spectrum directly (an open containing its closed point is the whole spectrum). The final dry run is rerun on these corrections before the push.
