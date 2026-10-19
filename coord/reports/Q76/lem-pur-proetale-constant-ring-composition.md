# Stage-1 report: lem-pur-proetale-constant-ring-composition

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-proetale-constant-ring-composition.json`: statement, now split into four elementary steps; preserved statement and existing metadata, added actual Mathlib searches. No new nodes, no Mathlib leaves.
- `citations.json`: seven verbatim statement quotations, one for each node used by each step.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `prepare.py` is sandbox-only preparation code, not a DAG delivery file.

## Attachments

None. Searched the whole read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag, constant-ring terminology and composition terminology. No exact finished declaration was found. Adic ring maps, structure-sheaf maps and module pullback composition do not state this finite constant-ring compatibility. The upstream master source is not being offered as proof evidence.

## WANTED

None. All sources needed for this argument are available locally.

## Findings and changes

The item was statement-only and has no blueprint_update. Its statement is correct and unchanged. The earlier item's Mathlib searches and blueprint ancestry were retained. The current unit record is sk-thm-smooth-purity; this sublemma supplies the coefficient compatibility needed in the ancestor's final composition step. The current blueprint places lem-pur-diagonal-base-change in sk-prop-sp-orientation; its last step still uses p_2 composed with Delta being the identity. No unit/chapter metadata or route was changed.

The whole-DAG and blueprint searches included constant ring, constant-section and Tag 09A5. `pur713-def-pullback-comparison` contains this argument as an explanation in a definition, and is already recorded in same_as. It is specialized to O_E/varpi^n and a Cartesian-square comparison; it is not used as a theorem proving the present statement for arbitrary finite commutative rings. We retain the reference and actually prove the compatibility here. The defining adjunction and constant-sheaf universal properties already exist, so no duplicate generic lemma or new node is needed.

The searches actually run for Q76 are exactly in searches.jsonl and were appended unchanged in tool/query to mathlib_searches. All four services succeeded. The two LeanFinder phrasings returned scheme structure-sheaf/module restriction comparisons and generic adjunction facts. LeanSearch returned sheafPullback, constantCommuteCompose, module pullbackComp and conjugateEquiv_pullbackComp_inv. Loogle's combined adjunction/constantSheaf pattern returned no hits. The Mathlib grep returned constantSheaf, constantCommuteCompose and global-section comparisons. I read ConstantSheaf.lean:184-203: constantCommuteCompose concerns a change of value category on one fixed site. It does not prove the specified constant-ring maps for composable scheme-induced pro-etale site morphisms. I also read Adjunction/Basic.lean:565-586; its composite Hom equivalence is exactly the definitional two-bijection calculation written out in the proof. There is no Mathlib match for the whole item.

## Review by Q76

I read Stacks proetale.tex, Tag 09A5 (section-morphism), in full through its initial site-morphism construction: inverse image is induced by base change. I read sites.tex, Tag 0H7J (example-constant-sheaf), and Tag 00WH (proposition-sheafification-adjoint), including the universal-property statement and proof. I checked the tag-to-label mapping. These sources supply the constructions, not a printed theorem asserting our full coefficient identity; proof_origin is therefore honestly agent-written. I read the current main-20261015 ancestor statement/proof and the current pur713-def-pullback-comparison, the shared DAG's expanded versions, and the unit's route. No SGA source is used. There are no new nodes whose sources need separate review.

For Step 1 I opened def-weil-proetale-inverse-image and def-weil-pbc-constant-sheaf. The former explicitly defines direct image by G(X times_Y V) and lifts its adjunction to ring sheaves; the latter explicitly gives the constant presheaf and identity restriction maps. Consequently restriction along the canonical base-change isomorphism preserves the constants by naturality of the sheafification map. We do not assume the coefficient isomorphism itself is strictly an identity, nor do we assume any connectedness.

For Step 2 I reopened both preceding definitions and def-weil-pbc-sheafification. The inverse-image node specifies exactly the rho maps sending a to a. The constant-sheaf node states that A_V is the sheafification of the constant presheaf. The sheafification node explicitly says every map to a sheaf factors uniquely, for rings as well as sets. Thus agreement on every a on every T is agreement as presheaf maps, and uniqueness proves equality of the full ring-sheaf maps. This proves the needed equality for locally nonconstant sections as well; it does not identify all sections with single constants.

For Step 3 the sole citation is def-weil-proetale-inverse-image. Its statement provides the ring-sheaf adjunction with unit/counit and defines c as the adjunct of rho. I wrote out both successive adjuncts, using naturality of eta_h at the correctly typed map c_k:L_k A_V to A_W. The first is rho_h composed with c_k, and the second is R_k(rho_h) composed with rho_k. This is an elementary calculation with the stated adjunction, not an uncited non-elementary coherence theorem.

For Step 4 the same citation supplies the adjunctions; alpha and the direct-image comparison beta are already specified by the item's own hypotheses. I stated the defining Hom-bijection compatibility of the unique left-adjoint comparison, with beta:R_k R_h to R_kh and alpha:L_kh to L_h L_k. These directions are important. With that definition, the adjunct of d composed with alpha is beta composed with the double adjunct from Step 3. Step 2 identifies this with rho_kh, and injectivity of the single adjunction bijection proves equality with c_kh. No isomorphism of arbitrary coefficient objects is being silently chosen, and no theorem about module/derived pullback is invoked.

Every cited node was checked in its statement, not in its proof; citations.json uses verbatim excerpts of those statements. The finite-commutative-ring hypothesis is sufficient for all specified coefficient objects, but the elementary compatibility calculation does not need finiteness. Scheme morphisms are arbitrary: no quasi-compactness, separatedness, properness or smoothness is used. The sites and ring adjunctions are those in the statement, with the same compatible skeletons/universes; no extra colimit or potentially large indexing category is introduced.

I tested the zero coefficient ring; empty Z and empty objects (the section set is a singleton and all constant values coincide); identity h or k with the specified canonical comparisons; and disconnected schemes, where arbitrary sections may be locally constant rather than constant. Sheafification uniqueness covers the disconnected case. None requires a correction to the statement. There is no new statement to test separately. Every proof step is under 1000 characters, hence none exceeds the long-step threshold. Each is a few-line restriction, universal-property or adjunction calculation, and none hides a non-elementary lemma.

Against delivery-errors B-E: the statement remains self-contained, sources use checked tags and labels, TeX is single-escaped in JSON, and there is no new node to carry a hidden proof, duplicate, clause restatement or unsearched Mathlib result. The four steps carry the argument themselves. Their uses equal proof_deps, their citations have exact statement support, and the route is unchanged. The coefficient-isomorphism theorem remains a statement dependency, as the unchanged statement explicitly refers to it; the proof does not need to invoke its isomorphism assertion.

## Not duplicates

No new nodes. Existing same_as pur713-def-pullback-comparison was retained for the specialized finite-coefficient comparison definition; no new copy was introduced.

## Unfinished work

None in the split. Server dry run and direct delivery follow this review; their output is the delivery record.
