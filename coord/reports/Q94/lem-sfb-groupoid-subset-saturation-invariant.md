# Worker report: lem-sfb-groupoid-subset-saturation-invariant

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-groupoid-subset-saturation-invariant.json: existing statement node, now split into three elementary assembly steps using an existing Mathlib leaf. Statement unchanged. Actual Q94 searches appended to the inherited Q68 searches.
- citations.json: one verbatim statement quote per step/node citation.
- report.md: this report. searches.jsonl is the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaf reused: lem-weil-pbc-base-change-image.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, saturation, groupoid, and GroupoidScheme/IsGroupoidScheme. The exact tag is absent. CategoryTheory.Over.DescentDatum.descent_orbit_saturated in AlgebraicGeometry/DescentOrbitSaturated.lean:43 proves a singleton-orbit assertion for a cartesian groupoid supplied by a descent datum, not the item for arbitrary groupoid schemes and arbitrary subsets. DescentNormAffineShrinking is also specialized. Neither is an exact attachment.

## WANTED

None. All sources used are present locally; no SGA source is used.

## Problems and corrections

The unsplit node had no proof. Its statement agrees with Stacks 03LO(1), together with the equivalence immediately after 03BC. There is no statement dispute and no change of hypotheses. The scheme groupoid definition supplies the required scheme-morphism equalities, not a groupoid structure on the raw topological points. Therefore a naive composition of two underlying points would leave a genuine gap: the two points must first be lifted to the scheme fibre product. This is supplied here by the already existing Mathlib leaf lem-weil-pbc-base-change-image, specialized to a singleton. I did not create a duplicate point-lifting lemma or a node restating the item.

The ancestor tool reports blueprint.from.node = None. I retain the item's inherited null ancestor and full via chain, and describe its place in split_report.blueprint. I read the latest blueprint's six-functor unit, its direct-image proof (3), and the chapter/unit records. The long recorded route through the alteration input remains unchanged; this proof is its generic groupoid-set tool. No unit record is changed because the item is not a unit's key node.

## Not duplicates

No new nodes were created. Whole-DAG searches included 03LO, 03BC, 022Q, 0232, fibre-product point-lifting, and the exact Mathlib name exists_preimage_pullback. Whole-blueprint searches with blueprint_refs.py for groupoid and fibre product points returned no statement equivalent to this item. In particular lem-a1-space-fibre-product-point is an existing more general space-point lifting tool; lem-weil-pbc-fibre-product-points parametrizes lifts by residue-tensor primes. The already existing base-change-image identity gives exactly the singleton lifting consequence needed, with no extra node or scheme-to-space comparison.

## Mathlib search results

Ran msearch.py for Q94 and this item with leanfinder (two phrasings), loogle, leansearch, and grep (two patterns). Read the returned types and source of PullbackCarrier.lean:295-309 and 410-429. Coverage saturation, subgroupoid generation, manifold structure-groupoid inversion, and gluing/restriction statements do not address internal groupoids of arbitrary schemes. Loogle returned zero hits. The grep did find Scheme.Pullback.exists_preimage_pullback and Scheme.image_preimage_eq_of_isPullback, the latter already represented exactly by lem-weil-pbc-base-change-image. Every newly recorded search entry is copied from searches.jsonl with its exact tool/query and actual result; no unavailable service is recorded as an absence. The old Q68 records are retained as inherited history, not claimed as Q94 calls.

## Review by Q94

I read groupoids.tex, Tag 03LO (lemma-constructing-invariant-opens), statement and proof of part (1); Tag 03BC (definition-invariant-open), including the following subset-invariance equivalence; Tag 022Q (lemma-pre-equivalence-equivalence-relation-points), including its common-field construction; and Tag 0232 (lemma-groupoid-pre-equivalence). These sources require no flatness, openness, separation, or finiteness for the subset assertion. Only parts (2) and (3) of 03LO impose extra hypotheses, and none are imported here. For the reused tool I read the entire statement and Mathlib match of lem-weil-pbc-base-change-image and verified the declaration in PullbackCarrier.lean:420 against it. I also read the entire statement of def-a1-groupoid-scheme and its source description (0231).

Step 1 uses precisely the equality for every subset C in lem-weil-pbc-base-change-image. With f=s, g=t, p=p_0, q=p_1 and C={r}, a is in t^{-1}(s({r})), because t(a)=s(r). The cited equality therefore produces z with p_0(z)=r and p_1(z)=a. Both maps have domain R and codomain U, and the chosen pullback is R times_{s,U,t} R. There is no smallness, rationality, closedness of points, or residue-field equality assumption. This singleton substitution is an elementary consequence of the cited statement, not an uncited appeal to the proof of a node.

Step 2 uses exactly sc=s pr_1 and tc=t pr_0 in def-a1-groupoid-scheme. I checked the projection order against that definition: c(z) has source s(a) and target t(r). Thus its source is in A and it witnesses t(r) in B. This proves the first inclusion by evaluating the defining morphism identities, without an additional theorem about composition on raw points.

Step 3 uses exactly si=t and ti=s from the same definition. Apply the already proved implication of steps 1 and 2 to i(r), whose source is t(r), and then substitute t(i(r))=s(r). This proves the opposite inclusion. Neither i squared equal to the identity nor surjectivity of i is needed. The citations.json quotes are literal substrings of the two cited statements, checked before writing.

I checked delivery-errors B1-B10: no new nodes, no claim of an exact attachment, no hollow or source-dependent statement, inherited fields retained, TeX written through JSON serialization, actual searches logged and read, and blueprint same_as checked. For C1-C8, every non-elementary input is the existing image-identity node, every cited node was opened, every use has a verbatim quote, the proof does not use a cited node's proof, and definitions/Mathlib leaves do not change the unit route. For D1-D5, the argument carries the actual composition and inversion rather than moving the conclusion to a new child; no induction or circular citation is used. For E1-E7, I checked the pullback, projection orientation, unrestricted hypotheses, and both inclusions explicitly. There is no source error in the portion used. No proof step exceeds 2000 characters.

Small cases checked: A empty gives both inverse images empty. A=|U| gives B=|U| using identity arrows. For the identity groupoid B=A and the equality is tautological. Empty U (and hence empty R) is vacuous. Nonclosed points and inseparable residue-field extensions are covered by the scheme fibre-product image identity. In the test Spec C over Spec R, the two distinct points in Spec(C tensor_R C) show why uniqueness of a point lift or identification with the topological fibre product is neither asserted nor used. No unproved new statement remains in this delivery.

## Unfinished work

None within this one-level stage-1 split. Independent maintainer review remains part of the normal delivery process.
