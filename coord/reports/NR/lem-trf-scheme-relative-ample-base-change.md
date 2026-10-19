# Stage-1 report: lem-trf-scheme-relative-ample-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-scheme-relative-ample-base-change.json: item split into five steps; statement and stmt_deps preserved exactly.
- dag/nodes/sec-trace-formula/lem-trf-scheme-relative-ample-affine-cover.json: new statement-only node, unsplit, no Mathlib match. It is the affine-cover criterion 01VJ (3) implies (1), without any base-change assertion.
- citations.json: one verbatim statement quotation for every node used by every item step.
- report.md: this report. searches.jsonl is the search command's own log.

## Attachments

None for the item or the new node. I searched the slopmaster2 project for the item id, its blueprint tag, relative ampleness, ampleness under base change, and local/relative ample declarations. There is no exact project declaration for the item. The field-extension and closed-immersion statements in Modules/Ample.lean and VeryAmple.lean have different hypotheses and cannot attach this item. The new affine-cover criterion has no project declaration either. The existing lem-weil-pbc-pullback-ample-invertible is already Lean-closed in its audit, and is reused, not restated or split.

## WANTED

None. Every source needed here is archived in literature/stacks-project/.

## Corrections and limits

The incoming node had no proof. Its statement is correct: absolute ampleness includes quasi-compactness, so its hypothesis already supplies the quasi-compactness in Stacks 01VH; this is Step 1, not an extra hypothesis. I kept its statement and all its original fields and searches. The original Mathlib search results have been read and reused. No compiler, Lean writing, target change, unit change, or route change was needed.

The initial draft mentioned the affine-open basis while citing only def-pc-scheme. During the C4 check I replaced this citation by the existing Mathlib leaf lem-weil-pbc-affine-opens-basis, whose statement supplies precisely the neighbourhood refinement used in Step 3. All proof steps are below 2000 characters.

The new node is intentionally unsplit: its non-elementary locality argument belongs to the next stage-1 item. It contains only its complete mathematical statement, and no proof or proof sketch. Nothing in this assigned one-level split remains unfinished.

## Not duplicates

lem-trf-scheme-relative-ample-affine-cover vs lem-trf-scheme-ample-canonical-proj-criterion: both cite 01VJ, but the existing statement gives (1) iff (5), involving the globally defined canonical section-algebra Proj map and quasi-compactness plus separation. It does not give the implication from ampleness over an affine covering, which is (3) implies (1). In particular its statement cannot be applied to the cover in Step 3 without additional gluing results.

lem-trf-scheme-relative-ample-affine-cover vs lem-pc-chow-relative-ample: both cite 01VJ, but the existing statement concerns a particular pulled-back twist in a proper Chow diagram and proves projectivity and two ampleness conclusions there. It has neither an arbitrary invertible module nor the cover-to-every-affine assertion.

lem-trf-scheme-relative-ample-affine-cover vs lem-trf-scheme-relative-ample-base-change: the new node is locality on a fixed base; there is no second base, fibre product, or pullback in its assertion. The item requires the affine pullback argument in Steps 3 and 4 before locality applies. This is not a restatement or a clause of the item.

The whole-DAG searches by 01VJ, lemma-characterize-relatively-ample, relative ampleness, affine covers and ample pullback found no existing affine-cover criterion. Whole-blueprint searches with blueprint_refs.py for ample, ampleness, relatively-ample, 01VJ and affine open covering likewise found no node stating it. The ancestor command gives lem-trf-local-term-locality; the new node records the item's ancestry with the item prepended to via. Historical polarized-descent ancestry is retained.

## Review by NR

I read Morphisms Tag 0893 (lemma-ample-base-change), its statement and entire proof, Tag 01VH (definition-relatively-ample), and Tag 01VJ (lemma-characterize-relatively-ample), including the proof of (3) implies (5) implies (4) implies (1). For the new node I checked the actual quantified hypotheses of 01VJ: h is quasi-compact, N is invertible, and the cover consists of affine opens whose full inverse images carry ample restrictions. Its conclusion is exactly (1) after expanding relative ampleness. I read 0892 (lemma-pullback-ample-tensor-relatively-ample), especially (2), and the proofs of 01SH and 01SD; I also read Schemes 01K5 for the quasi-compact base change used in Step 2. These are supporting inputs of the 0893 proof, not replacements for the unit route.

For Step 1 I opened def-weil-pbc-ample-invertible-module and def-weil-finite-type-morphism. The former requires its whole scheme to be quasi-compact, and the latter defines quasi-compactness of f by the quasi-compactness of all affine-open inverse images. The inference is just these two definitions; it neither uses nor asserts finite type.

For Step 2 I opened lem-weil-pbc-invertible-pullback-tensor and lem-pc-quasi-compact-base-change. Clause (1) of the former explicitly preserves invertibility under every scheme morphism. The latter explicitly permits arbitrary g and requires only quasi-compactness of f, now supplied by Step 1. This verifies both hypotheses later needed for the local criterion, even when the bases are non-Noetherian or g is not flat.

For Step 3 I opened lem-weil-pbc-affine-opens-basis and def-pc-fibre-product. The basis node explicitly gives an affine neighbourhood contained in any specified open. Applied to the whole target and then the inverse image of that target neighbourhood, it supplies U_i and U'_i. The definition of fibre product gives its complete universal property, so I wrote out the identification of the restricted product and its projection. No statement that an arbitrary affine open of T' maps into a single affine open of T is made.

For Step 4 I opened lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-pullback-ample-invertible, and def-pc-module-pullback. The first states affineness for every map between two affine schemes. Clause (1) of permanence preserves it under every base change, so a_i is affine without requiring Z_i to be affine. The ample pullback node assumes exactly an affine morphism and an ample invertible module, both in force. The pullback definition explicitly includes composition isomorphisms, which identify the restriction of g'^*L with a_i^*(L restricted to Z_i) because their maps to X are the same. The needed restriction-to-open identification is obtained directly by restricting the displayed tensor-pullback formula. Thus no stronger theorem is taken from any cited proof rather than its statement.

For Step 5 I re-read the new affine-cover node against 01VJ. Its cover is precisely the one constructed in Step 3; invertibility and quasi-compactness were verified in Step 2 and all local ampleness assumptions in Step 4. It gives every affine open V' of the entire new base. It does not merely prove ampleness on the initially chosen cover. citations.json copies the complete actual statements, so each cited part can be checked verbatim.

I checked small cases for the item and new node. Empty base or empty source gives only empty inverse images, which are quasi-compact and satisfy ampleness vacuously. An empty cover is possible only for an empty base. For the identity base map the construction returns the original relative ampleness. On P^1_A with O(1), pullback along Spec B to Spec A gives the usual O(1) over B with no finiteness or flatness assumption; O and O(-1) on P^1 over a field do not satisfy the ample hypothesis, so no invalid conclusion follows for them. For an infinite disjoint union of affine base components the proof uses the full open covering and does not presume the base or its cover finite. A non-quasi-compact source with trivial invertible module cannot slip through Step 1 or the new node's explicit quasi-compactness hypothesis.

I checked B1-B10: new-node form, introduced objects and definition dependencies, single TeX escaping, correct Stacks labels, actual logged searches, exact-match criteria, blueprint provenance and project attachment searches. I checked C1-C8 by opening every cited statement as described above; existing affine geometry and ample-pullback nodes are reused, and there is no new dependency back to the item. The only non-leaf generic off-unit tool is lem-weil-pbc-pullback-ample-invertible, declared in split_report.tool_uses; it is in fact already Lean-closed. I checked D1-D5: Steps 3 and 4 carry the base-change argument, and the new locality node does not restate it or hide the entire item. I checked E1-E7: no Noetherian, finite type, separated base, finite covering, flatness, or surjectivity assumptions are used. No source error or statement dispute was found. No SGA source is used.

For the new node the two LeanFinder phrasings and LeanSearch returned generic affine-local morphism-property infrastructure, not a relative ampleness theorem. I read Mathlib/AlgebraicGeometry/Morphisms/Basic.lean at the HasAffineProperty class and its cover lemmas: those results already assume the local property they transport, so they do not supply the missing ampleness-locality theorem. Loogle returned no IsAmple declaration. The sole grep hit was an unrelated example for isomorphisms in Morphisms/IsIso.lean, not an ampleness definition or theorem. Every new-node query matches searches.jsonl; no unrun query or unavailable service is reported as a negative result.
