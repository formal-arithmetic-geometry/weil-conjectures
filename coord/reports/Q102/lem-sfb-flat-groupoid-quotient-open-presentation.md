# Stage-1 delivery: lem-sfb-flat-groupoid-quotient-open-presentation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-groupoid-quotient-open-presentation.json: split item, eight steps; no exact project attachment or Mathlib match found.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-finite-fppf-descent.json: new statement-only lemma; no Mathlib match. It states descent of finiteness for algebraic spaces along an fppf covering, not a quotient-stack clause.
- citations.json: exact statement text for every proof citation.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag and for quotient-stack, flat-groupoid and presentation terminology; no declaration states the whole item. Sorry declarations would not qualify.

## WANTED

None. All mathematical inputs used are in the local Stacks source.

## Corrections and scope

The mathematical statement is unchanged. Doubled TeX escapes in the imported statement were normalized. Inertia and separation conventions in its preamble are redundant but retained. The existing invariant-open descent theorem assumes a smooth atlas, so applying it directly to the merely flat presentation would be invalid. The proof instead passes through a smooth atlas A and explicitly proves saturation and invariance on its common pullback with U. The finite-presentation clause uses local finite presentation together with affineness, quasi-compactness and quasi-separatedness, never the false assertion that an arbitrary finite morphism is finitely presented.

The current latest blueprint proof of det-thm-sf-ctf-stability-direct-images (3) was read. This is a supporting quotient-geometry input below that route, not a key unit node, so no unit realization field is changed. The ancestor command returns blueprint.from.node = None; this agrees with the live support node's inherited provenance and is retained. Its detailed from.place and via chain are retained and extended for the new support node. Whole-blueprint groupoid, open-substack, finite-morphism, finite-descent and finite-locally-free searches gave no exact equivalent blueprint statement.

## Not duplicates

lem-sfb-space-finite-fppf-descent vs lem-sfb-finite-space-morphism-topology: the existing node gives base-change stability, closedness, finite fibres and local quasi-finiteness of a map already finite on scheme tests. It does not descend finiteness from an fppf cover; the new node does. The existing node supplies base change in steps 2 and 8.
lem-sfb-space-finite-fppf-descent vs lem-sfb-space-relative-spec-correspondence: that node gives the anti-equivalence between affine spaces and quasi-coherent algebras, including recognition of finiteness under that anti-equivalence. It assumes an affine space or a quasi-coherent algebra and does not assert effective descent of finiteness for an arbitrary algebraic-space source on an fppf cover. The new node supplies precisely that missing locality assertion.

The flat-groupoid algebraicity and fppf-presentation nodes already cover the algebraic-stack and kernel-pair clauses and are reused. The finite-flat quotient-open geometry node assumes a Deligne--Mumford quotient, which this item does not; it cannot replace the invariant-open argument here. The invariant-open substack node has a smooth-atlas hypothesis, verified at A and never asserted for U. Existing scheme finiteness descent cannot be applied to F before its scheme representability is known, so the algebraic-space descent node is necessary.

## Review by Q102

I read criteria.tex, Tag 06FH (lemma-flat-quotient-flat-presentation), including its local-object-lift proof, and Tag 06FI (theorem-flat-groupoid-gives-algebraic-stack); spaces-groupoids.tex Tag 04M9 (lemma-quotient-stack-2-cartesian); stacks-properties.tex Tag 0507 (lemma-substacks-presentation), including the smoothness used in its proof; algebraic.tex Tag 04WY (remark-flat-fp-presentation); and stacks-morphisms.tex lemma-points-presentation. For the new node I read spaces-descent.tex Tag 0426 (lemma-descending-property-finite) and spaces-morphisms.tex Tag 03ZQ (lemma-integral-local), finite case. I also read the base-change finite case of Tag 03ZS, and morphisms.tex Tag 01S7 for the affine permanence check.

Step 1 uses the full statement of the existing flat-groupoid algebraic-quotient node: it gives all atlas properties, the kernel pair and field-extension point lifting under exactly flat and locally finitely presented s,t. Schemes over Spec k are permitted algebraic spaces. No smoothness of s,t is assumed.

Step 2 uses stackification's local essential-image clause, not an undocumented torsor description. Its 2-fibre-product tuples identify the pulled-back map with R times_U T_i. The existing finite-space topology node gives finite base change; the new node gives descent even when F is initially only an algebraic space. The finite-morphism definition gives affine scheme tests, and affine-morphism permanence gives quasi-compact and quasi-separated tests. Thus finite presentation is justified without Noetherian assumptions. I removed base-change and affine-permanence clauses from the new node after finding these existing statements.

Step 3 uses only the explicit open-substack and tuple definitions. It does not take the conclusion of smooth-atlas descent at the nonsmooth U.

Step 4 chooses the smooth atlas from the algebraic-stack definition, uses the chartwise calculus for its base changes and for flat local finite presentation of q, the representable point-surjectivity equivalence to justify surjectivity on point sets, and the universally-open space lemma for the image of D. The point-fibre-product lemma supplies the common-field pair (e,d). Invariance on R makes D saturated. Only the open-subspace/point-subset correspondence of the etale-open-image node is used here, not its etale-image theorem for the flat map q.

Step 5 writes the comparison arrow and its inverse explicitly, showing B is invariant on the smooth atlas relation. The smooth-atlas invariant-open theorem therefore applies with all its hypotheses verified. Step 6 checks the two pullbacks on E, descends equality by point surjectivity, and invokes uniqueness and inclusion preservation only on that smooth atlas. This avoids using a node's proof as though it were its statement.

Step 7 uses stability of representable flat, locally finitely presented surjections, and clause (2) of the fppf-groupoid-stack-presentations node, which explicitly identifies an algebraic stack with the quotient of its fppf self-relation. It gives the displayed restricted quotient, after the endpoint condition identifies the restricted relation with either inverse-image open. Step 8 uses the finite-space base-change clause and the chartwise flat/local-presentation clauses; the finite-locally-free node is used only for its definition. No separate elementary restriction node is created.

I checked every cited node's statement, and citations.json contains its verbatim text. Generic off-unit tool uses are declared in split_report.tool_uses; they do not replace the unit's alteration route. The new node is self-contained, has no proof or proof dependencies, and all its search entries come from searches.jsonl. Two semantic phrasings and name/pattern queries were read: the hits are scheme-only IsFinite, its base-change instances, and flat-descent results. Their source signatures quantify over Scheme, so they do not give the new algebraic-space assertion by one-line specialization. No Mathlib leaf is claimed.

Edge cases checked: U and R empty; V empty or all of U; identity groupoid on an arbitrary non-Noetherian or non-quasi-compact scheme; finite flat non-etale group schemes (e.g. alpha_p in characteristic p); nonsurjective V into U; and nontrivial stabilizers. The argument uses neither a Deligne--Mumford assumption nor freeness of the groupoid, nor separatedness of U. For the new node an empty target/empty covering is harmless, and no individual covering member is required to be surjective. Finite on scheme tests includes representability, so that conclusion is not silently assumed. Every non-elementary step has explicit node citations; none exceeds 2000 characters or hides a separate standard comparison. The open correspondence is proved through saturation, rather than moved into a new node. Sections B--E were checked for statement-only form, exact source tags, real searches, duplicate and elementary-node avoidance, citation sufficiency, hypotheses and acyclicity.

## Unfinished

No part of this one-level split is intentionally unfinished. The new statement-only finiteness-descent lemma remains for the stage-1 queue as required.
