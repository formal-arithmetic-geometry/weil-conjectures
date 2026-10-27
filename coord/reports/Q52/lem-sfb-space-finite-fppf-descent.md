# Stage-1 report: lem-sfb-space-finite-fppf-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-finite-fppf-descent.json: statement, split; not a Mathlib leaf. Six proof steps using existing nodes only. The statement and stmt_deps are unchanged.
- citations.json: fourteen step/node entries containing verbatim statement excerpts.
- searches.jsonl: actual msearch.py logs; the pre-existing search records in the item were retained and the searches of this session appended.
- report.md: this report. write_split.py is a sandbox-only writer, not part of the delivery.

There are zero new nodes and zero new Mathlib leaves.

## Attachments

No attachment for the item. Searches for its exact blueprint tag and the finite/algebraic-space/descent notions in lean/WeilConjectures found no declaration stating the full item. Scheme descent is already stated and proved as AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact, lean/WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean:106; this belongs to the existing lem-sbc-finite-morphism-fpqc-descent and is used through that node. This is not a claim that its wider transitive sorry audit has been rerun.

## Literature

No WANTED sources. Read Stacks spaces-descent.tex Tag 0426 (lemma-descending-property-finite), its affine-descent proof Tag 041Z (lemma-descending-property-affine), and the general affine reduction (lemma-descending-properties-morphisms). Also read spaces-morphisms.tex Tag 03ZQ (lemma-integral-local), its scheme-test definition and finite-integral comparison; spaces-topologies.tex Tag 0DFQ (lemma-zariski-etale-smooth-syntomic-fppf-fpqc); descent.tex Tag 02LA (lemma-descending-property-finite); and morphisms.tex Tag 01WI (lemma-finite-local) and lemma-base-change-finite. All are in the supplied literature. No SGA used.

The proof is marked agent-origin: it assembles space affineness descent, finite affine refinements, and scheme finiteness descent, rather than copying the integral plus locally-finite-type decomposition in 0426. It retains the same finite-descent input to the groupoid route. Read the chapter and unit records and the latest blueprint direct-images proof (3); none of their routes is replaced.

## Corrections and limitations

The imported item was a statement-only node, without proof or Lean attachment metadata. Its statement is correct and is not disputed. The title mentions base change, and the first step explicitly proves stability under arbitrary algebraic-space base change from the scheme-test definition, as well as the stated forward implication. No hypotheses are added.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor prints None. The detailed inherited place and via chain are retained, and same_as is [] after whole-blueprint searches for 0426, finite fppf, finiteness descends, fppf descent, and finite morphism. The current direct-images proof (3) is an assembly by compactification; the long inherited helper chain is historical below that input. No blueprint metadata or chapter/unit binding is invented to replace that history.

Nothing mathematical remains unfinished for this one-level split. Its existing unsplit dependency lem-sfb-space-fppf-finite-affine-refinement remains a separate item; this delivery neither splits nor edits it.

## Not duplicates

No new nodes were created. The existing lem-sfb-space-integral-finite-etale-locality gives etale locality, which alone does not establish descent for the given fppf family. The existing lem-sfb-space-four-property-fppf-descent gives affineness descent but omits finiteness; it is reused only for affineness. The existing finite affine refinement and scheme finite-descent nodes provide the other ingredients. Thus there is no reason to duplicate any of them.

## Mathlib searches

Ran the mandated msearch.py leanfinder, loogle, grep and leansearch commands, followed by another LeanFinder phrasing and another grep. Read their actual outputs. All services answered. The Loogle IsFinite hits and LeanFinder candidates are scheme statements; Finite.lean:35-77 confirms the category Scheme and its base-change/affine-ring criteria. FlatDescent.lean's generic fppf/fpqc comparison also has category Scheme, and the project finite-descent declaration is about Scheme. The LeanSearch local representability result is for a scheme topology, not a theorem descending finite algebraic-space morphisms. No candidate states this item or specializes to it in one line. Logged queries are copied verbatim into mathlib_searches. Earlier searches in the live item are preserved as history, without claiming to have run them in this session.

## Review by Q52

I checked the item directly against 0426 and 03ZQ: the finite condition includes representability by schemes, not just a module-finiteness predicate on a previously assumed scheme source. The refinement argument works for arbitrary base schemes, arbitrary set-indexed covering families and non-quasi-compact covering members. No Noetherianity, finite type or separatedness assumption has entered the statement. There are no new-node sources to audit.

In step 1, the fibre-product node explicitly gives both the algebraic-space fibre product and its categorical universal property. The displayed iterated-pullback identification preserves the projection to the scheme test; the finiteness assertion is consequently precisely an assumed scheme test. This is genuinely elementary and does not need a new base-change lemma.

In step 2, the definition of finite scheme morphisms explicitly includes affineness, and affine-morphism permanence (2) gives an affine source over an affine target. This verifies the definition of affine space morphism used by the four-property descent node. That node explicitly states the fppf equivalence separately for affine, finite type, quasi-finite and separated; only its affine clause is used. The space-affine-locality node explicitly states base-change stability and that an affine space over a scheme is a scheme. This ensures that every later application of a scheme theorem has scheme objects already in hand. It avoids assuming what finite descent must prove.

In step 3, I read the entire finite-affine-refinement statement: it supplies the finite index set, the factorization through the particular Y_i, affineness of the coproduct, and flatness and surjectivity of its map to T. It applies because the original family has exactly its chartwise flatness/local finite presentation and point-surjectivity hypotheses. The projection-preserving fibre-product reassociation makes each local projection a scheme test of the assumed finite f_i. No claim about arbitrary flat base change of an atlas was taken from the etale-cover clause of the fibre-product node.

In step 4, the scheme-coproduct statement explicitly supplies an open covering by its summands. The finite-local-on-target statement explicitly allows an arbitrary open cover, not merely an affine singleton; its clause (3) proves the coproduct projection finite. This replaces the initially considered coordinate-product argument, so no unrecorded finite-module descent, affine-ring comparison or product-module theorem is hidden here. The restrictions agree by the same pullback universal property cited in the step.

In step 5, I checked the morphism-between-affines node and affine permanence (3), which together give the quasi-compactness not explicitly asserted as a standalone clause by the refinement node. The scheme finite-descent statement requires precisely flat, surjective and quasi-compact; those three conditions are now verified for p. It assumes no finite presentation of f_T. Its input after base change is exactly step 4. This is a generic tool from another unit, recorded in split_report.tool_uses, not a replacement for a unit route.

In step 6, representability for an arbitrary scheme T was already established in step 2. The restrictions to affine opens U are exactly the tests treated in step 5. The same finite-local-on-target clause (3), now applied to the affine open cover of T, proves finiteness for every scheme test as the item requires. Thus neither affine tests alone nor representability alone is incorrectly declared to be the entire conclusion.

For small cases I checked Y empty and the empty family, an identity cover, and covers with empty members. The finite refinement allows J empty for T empty. The coproduct source over the empty scheme is empty and the empty open-cover finiteness criterion applies; no nonempty finite set is chosen. Non-quasi-compact bases are handled one affine scheme test at a time. I checked the union of all step uses equals proof_deps, every citation has its stated exact quote, no step exceeds 2000 characters, and the cited closures do not return to the item. There is no new clause-node or hidden lemma merely renaming the desired conclusion.
