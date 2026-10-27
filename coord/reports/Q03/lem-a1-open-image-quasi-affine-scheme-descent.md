# Q03 stage-1 report: lem-a1-open-image-quasi-affine-scheme-descent

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-open-image-quasi-affine-scheme-descent.json`: item, statement unchanged, split into seven proof steps. Mathlib verdict: no exact match.
- `citations.json`: 16 step/node pairs, with verbatim excerpts checked against the cited statements.
- `report.md`: this report.
- No new nodes and no new Mathlib leaves. `searches.jsonl` records five searches actually run by msearch; `index.json` and `write_split.py` are sandbox-only working aids, not delivery nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and quasi-affine descent terminology. The related theorems in `AlgebraicGeometry/Sites/EtaleTopologicalInvariance/Descent.lean`, especially `AlgebraicGeometry.Scheme.Hom.exists_isQuasiAffine_etale_obj_iso_of_etale_cover`, require etale objects and a universal homeomorphism. They do not state this item, which concerns an arbitrary quasi-affine pullback of an algebraic space. No attachment is claimed.

## Wanted literature

None. All sources used are available in the read-only literature checkout.

## Corrections and scope

The imported item had no proof, so its implicit covering and identification arguments were missing. Its statement is correct and is retained verbatim. In particular no separatedness, local quasi-finiteness or finite-presentation hypothesis on W was added. Those hypotheses occur earlier in the proof of Stacks 03XW to establish quasi-affineness, but this item already assumes the needed quasi-affine morphism P to T'.

The notation of 03XW uses U for our W and W for our B. Its last paragraph also says U' where the previously constructed object is T' times_T U. The split uses the explicit object P throughout. This is only a notation clarification; it causes no statement dispute.

The blueprint ancestor `lem-a1-affine-hc0` proves vanishing by support on a connected nonproper curve. This item is a historical geometric support ingredient below that node, through the existing representability chain, not a replacement proof of the Rankin–Selberg unit. The unit's key node is not this item, so no unit realization record was edited.

## Unfinished work

None at this split level. Existing unsplit descendants, notably `lem-a1-space-open-factor-scheme-tests`, remain independently assigned DAG tasks. They are reused by their stated conclusions, not treated as completed Lean proofs.

## Not duplicates

No new nodes were created. Searched the full DAG statements and source places and ran blueprint searches for `quasi-affine` and `descent datum`. Existing Tags 03IE/06NF, 01S8/01SD, 022C, 02W5 and 0247 nodes cover the tools needed; none was recreated. In particular the general quasi-affine fpqc effectivity theorem and the fppf sheaf/descent-data equivalence already exist in sec-trace-formula. The item assembles these with the open-image and covering arguments; it is not replaced by a new node restating its clauses.

## Review by Q03

I read the item, the chapter and unit records, GOAL.md, the stage-1 contract, and delivery-errors B–E, including both copies of those sections. I read Stacks `spaces-morphisms.tex`, Tag 03XW (`lemma-neighbourhood-scheme`), including the preceding induction and quasi-affineness construction and the final sheaf-descent paragraph. For the expansion I read `spaces-properties.tex`, Tag 03IE (`lemma-factor-through-open-subspace`) and Tag 06NF (`lemma-etale-image-open`); `morphisms.tex`, Tags 01S8 (`lemma-characterize-affine`), 01SD (`lemma-base-change-affine`) and 03WT (`lemma-etale-open`); `topologies.tex`, the fppf-covering definition and Tag 022C (`lemma-zariski-etale-smooth-syntomic-fppf-fpqc`); `spaces.tex`, Tag 025Y and the open-subspace definition; and `descent.tex`, Tags 02W5 (`lemma-descent-data-sheaves`) and 0247 (`lemma-quasi-affine`). There are no new-node sources to review. I reopened every cited node JSON and checked the statement, rather than borrowing a construction from its proof.

Step 1 uses the exact open-map conclusion of `lem-weil-pbc-etale-morphism-open-map` to obtain the open B. `def-a1-space-open-subspace` explicitly says W is an algebraic space, and `def-trf-scheme-algebraic-space` allows treating T, T' and B as their representable sheaves. `lem-a1-space-open-factor-scheme-tests` explicitly supplies the point-image factorization, preservation of etaleness and surjectivity for equality of the image, and the comparison of products over B and T. Its hypotheses are satisfied: B is open, W's image is contained in B, and a's image equals B. This is the open-subspace factorization case, not the invalid inference of factorization through an arbitrary immersion flagged in E3.

Step 2 uses `pqf-lem-affine-local-target` in its affine-open-cover direction with the single open T; its inverse image is the entire affine scheme T'. The universal property in `def-pc-fibre-product` identifies the pullback along B with T'. Clause (1) of `lem-weil-pbc-affine-morphism-permanence` gives affineness after this arbitrary base change, and clause (3) gives quasi-compactness. Neither assertion assumes B affine. This avoids requiring the affine source to imply an affine morphism into an arbitrary target.

Step 3 uses the explicit flat and locally finitely presented clauses of `def-weil-etale-morphism`. Together with surjectivity these are exactly the covering definition in `def-pc-fppf-site`. `lem-trf-fppf-covering-is-fpqc` states that this same family is fpqc, so no unstated quasi-compactness criterion is used. The family has one member throughout.

Step 4 is elementary sheaf gluing after the cited definitions. `def-a1-space-open-subspace` supplies W's algebraic-space property, `def-trf-algebraic-space` supplies its actual fppf sheaf, and `def-trf-scheme-algebraic-space` supplies the sheaf h_B. A cover in Sch/B is the same family on underlying S-schemes. I wrote out both gluing in W and the local equality of its composite to B with Q's structure map. Thus the sheaf obtained is exactly the fibre functor in the statement, with no implicit fpqc site or replacement of the original W.

Step 5 uses the statement of `lem-trf-fppf-sheaf-representability-descent-data`: locally representing schemes are the objects of the associated datum, and their comparison isomorphisms give it. The cover is fppf by Step 3; its pullback representation is P by Step 1 and the test-point description. The explicit map ((w,t0),t1) to (t0,(w,t1)) fixes the ordered overlap coordinates. On a triple overlap each path retains the same w and moves the distinguished coordinate from t0 to t2, giving phi02 = phi12 composed with phi01. No arbitrary isomorphism of the two products is substituted for this comparison.

Step 6 uses exactly `lem-trf-quasi-affine-fpqc-effective-descent`, with A=T', base B, V=P and the datum of Step 5. I checked all three nontrivial hypotheses: singleton fpqc covering, the assumed relative quasi-affine morphism, and the cocycle. The statement imposes no affineness on B and no local finite presentation on P to T'. Its conclusion is precisely effectivity with an identification inducing the datum.

Step 7 uses the final iff in `lem-trf-fppf-sheaf-representability-descent-data`. Since the datum was constructed from the specified sheaf and is effective, this iff identifies that sheaf as representable. This checks the identity of the represented object, in addition to the existence of some descended scheme.

The two sec-trace-formula statements are generic descent tools. Their uses are declared in `split_report.tool_uses`; no unit step is replaced by a different route. All other off-unit statement tools used are existing Mathlib leaves, and definitions are used as notions.

I checked the edge cases T'=empty (hence B=empty and W=empty by the open-factor statement), W=empty with nonempty B, a not surjective onto T, and a non-affine open B. The argument never replaces B by T or asserts B affine. Arbitrary S and a non-quasi-compact W remain allowed. Each step is under 900 characters, so none conceals a long-step lemma. The item and cited statements have no dependency path back to this item. The proof dependency list is exactly the union of step citations; sources, blueprint ancestry and imported metadata are retained. All 16 quotes are literal substrings of the corresponding cited statements. There are no new nodes requiring definition-completeness or duplicate-pair repair.

The Mathlib queries were run by the mandated msearch command and their results read. Loogle and grep returned no hits. The two LeanFinder phrasings returned Zariski local representability and scheme morphism-descent results; LeanSearch returned absolute quasi-affineness and scheme morphism properties. These do not state the algebraic-space open-image/sheaf statement. Inherited searches of the item's creator were retained separately. No unavailable service was recorded as absence.

## Validation

The required server dry run passed: `OK (not pushed) deliver/Q03/lem-a1-open-image-quasi-affine-scheme-descent at 35e9c6b3be4: preflight passed`. The first completed invocation rejected the Step 2 fibre-product quote because it was shorter than 40 characters; I replaced it with the full 228-character universal-property clause. The successful invocation checked the corrected citations and ran the maintainer preflight on the server. No Lean was written or compiled. The delivery command reruns preflight before pushing.
