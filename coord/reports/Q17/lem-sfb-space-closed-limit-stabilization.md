# Stage-1 report: lem-sfb-space-closed-limit-stabilization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-limit-stabilization.json: existing statement, now split into six proof steps; not a Mathlib leaf.
- citations.json: one entry per cited node per step, quoting its entire statement verbatim so no qualifier is omitted.
- searches.jsonl: actual msearch records; inherited search records in the item retained and five current searches added.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this supporting item is not the unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and closed-limit/stabilization terminology, and inspected inverse-limit search hits. There is no declaration stating every clause for algebraic spaces. Scheme declarations and sorried source material do not attach this item.

## WANTED

None. All proof sources needed here are present in literature/stacks-project/.

## Corrections and unfinished work

The statement is correct as written and was retained exactly. The imported item had no proof. I supplied the affine-chart reduction, explicit verification of every scheme-stabilization hypothesis, and the descent of the resulting isomorphisms. I retained every inherited field and search. No mathematical work is unfinished.

The ancestry helper reports blueprint.from.node = None for this item, exactly as inherited; its long from.place and via list were retained. The latest blueprint was read under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/: the unit and the direct-images proof (3). That current text gives compactification assembly rather than the old expanded alteration argument. This supporting input remains the 0828(3) step already required by its parent lem-sfb-space-eventual-monomorphism; no unit route is changed.

## Mathlib and duplicate searches

Searched the whole DAG by Tag 0828, finite-type-eventually-closed, finite-presentation-permanence and closed-limit terminology. Used tools/blueprint_refs.py search for closed immersion, stabilization, and 0828, and ancestor for this item. The existing lem-weil-pbc-closed-limit-lfp-stabilization supplies exactly the scheme case, and lem-sfb-space-relative-lfp-permanence supplies 05WT; neither was duplicated. The existing atlas and affine-limit nodes supply the remaining geometry. No new node is proposed, so there are no new/existing same-tag pairs requiring a Not duplicates table.

Ran msearch for two LeanFinder phrasings, Loogle with "IsClosedImmersion", "IsLimit", a global algebraic-space/closed-limit grep, and LeanSearch for the whole assertion. All services answered. The hits concern schemes or profinite spaces, not this assertion for algebraic spaces. Read Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean at lines 635–645 and 690–703, Morphisms/FinitePresentation.lean at 35–47, and Morphisms/Separated.lean at 128–136. These candidates have Scheme objects. The global grep returned no algebraic-space declaration. The item keeps the old searches and records only the new queries actually run.

## Review by Q17

I read Stacks spaces-limits.tex, Tag 0828, the entire statement and proof, concentrating on (3), together with Tag 07SF's affine-limit construction and base-change formula. I read spaces-properties.tex Tag 03H6 and spaces-morphisms.tex Tags 05WT, 0410 and the source-and-target chart criterion. I also read limits.tex Tag 081B(3) and its affine proof. These are the source's own affine-chart route. No new node needs a separate source audit.

For step 1 I opened lem-sfb-space-relative-lfp-permanence: it says precisely that C -> C_a is locally of finite presentation when C -> B is and C_a -> B is locally of finite type. Both hypotheses are assumed, with no separation assumption. The tail argument is written out, including independence of a chosen common upper bound; a tail has the same categorical limit.

For step 2 I opened lem-trf-space-qc-finite-affine-atlas-refinement: its final clause gives an affine surjective etale atlas under exactly our atlas definition of quasi-compactness, without quasi-separatedness. I checked def-weil-closed-immersion's affine-quotient characterization and the scheme base-change statement of lem-weil-pbc-closed-immersion-base-change. Representability in the item's definition makes U_i schemes; the repeated-fibre-product identity identifies each transition with the required scheme base change. The affine quotient makes each U_i affine, and lem-weil-pbc-affine-scheme-qcqs gives quasi-compactness. The quotient algebra is generated over the source ring by the empty set, so the actual definition def-weil-finite-type-morphism proves the needed local finite type without a hidden finiteness theorem.

For step 3 I opened lem-sfb-space-affine-limits-schematic-stages in full: its first, unconditional clause gives the sheaf limit and affine projections, and its last clause gives arbitrary base change of the limit. I use neither of its eventual-schematicity clauses, which would require qcqs stages. Closed immersions are affine directly by their scheme-test/affine-quotient definitions. The sheaf limit is a limit over B, so uniqueness identifies it with the C in the hypothesis; no assumption that the given limit was already a sectionwise sheaf limit is silently imposed. I added def-trf-scheme-algebraic-space and wrote the evaluation-at-the-identity argument identifying natural transformations between representables with scheme morphisms. This justifies that the affine chart cone is a scheme limit.

For step 4 I opened lem-sfb-space-local-properties-chart-test: take target atlas U_a -> C_a and identity source atlas of C x_(C_a) U_a = U. Step 3 guarantees this object is a scheme, and step 1 gives the property being tested. Thus its conclusion is exactly local finite presentation of U -> U_a. The proof does not incorrectly treat the algebraic-space base B as a scheme or claim that local finite presentation to B is already finite presentation to U_a.

For step 5 I opened lem-weil-pbc-closed-limit-lfp-stabilization and checked every hypothesis with base U_a: small nonempty directed tail, quasi-compact affine U_i, locally finite type quotient structure maps, closed immersion transitions, scheme limit U, and local finite presentation U -> U_a. Its statement gives the canonical projections as isomorphisms at every later stage, exactly the conclusion needed on the atlas. This is a generic scheme tool explicitly used in the source 0828(3); its off-unit use is declared in split_report.tool_uses, and no unit-route step is replaced.

For step 6 I opened lem-trf-space-fibre-products-etale-covers and checked that its cover base-change clause gives U_i -> C_i and the cover after every scheme test. I opened def-weil-etale-morphism and def-pc-fppf-site to verify that the surjective etale scheme test is an fppf cover. I opened def-trf-algebraic-space to verify that C is an actual fppf sheaf and morphisms are natural transformations. The local inverse is unique on the cover and double overlap, so the sheaf equalizer glues it uniquely. This is a direct sheaf-axiom argument, marked elementary and written out, not an uncited isomorphism-descent theorem.

I tested the empty C_a case (empty affine atlas Spec 0), empty limit, a singleton index, a constant system, and a directed set without a least element. Empty limits do not cause the argument to presume nonempty stages: the scheme stabilization theorem still applies. The singleton case merely recovers the given identity projection. The tail construction handles the absence of a least element. I verified by reading dependency closures that the substantive existing nodes cited do not depend on this item. The split has no new statements, no restatement node, no hidden long step (each is below 2000 characters), no new axioms, no SGA source, and no Lean writes or compiler invocation.

## Server validation

The first required deliver.py dry run exited OK with server preflight passed. A final text audit caught two tab escapes in the representable-sheaf arrows, which were corrected; the final dry run is repeated on that corrected text before pushing. No server checks are run locally.
