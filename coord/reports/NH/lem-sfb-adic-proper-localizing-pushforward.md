# Repair: lem-sfb-adic-proper-localizing-pushforward

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adic-proper-localizing-pushforward.json: unchanged statement and statement dependencies; 936-character assembly proof and declaration allocation map.
- dag/nodes/sec-six-functors-basics/lem-sfb-adic-proper-localizing-membership.json: statement, unsplit, no Mathlib match; preserves the complete closure and specialization argument in source.note.
- dag/nodes/sec-six-functors-basics/lem-sfb-adic-proper-localizing-restricted-coproducts.json: statement, unsplit, no Mathlib match; preserves the complete restriction and colimit-reflection argument in source.note.
- citations.json: retained verbatim quotations covering every citation in the parent's three proof steps.

There are two new nodes and zero Mathlib leaves. Both children have no proof, proof_deps, proof_origin or lean field. Their Lean allocations are suggestions for later binding, recorded by the supported split_report map, not maintainer-owned metadata. No Lean was written or compiled.

## Attachments

None. The human explicitly reopened this item to distribute two declarations on a sorry route. No completed-proof attachment or closed-axiom claim is made.

## WANTED

None. The latest restriction proof and the existing DAG statements provide the construction material; this is an agent-written categorical expansion, with no SGA source.

## What was wrong and what changed

The earlier brief required child lean fields, which the stage-1 packager strips. The human's restatement of 2026-10-27 14:50 CST resolves that conflict: lean is maintainer-owned, and a split_report.lean_declarations dictionary plus this report records the requested allocations. I removed both child lean fields, removed proof/proof_deps/proof_origin, and moved all four retained construction paragraphs into source.note. I additionally copied the original live parent's three argument texts verbatim into the corresponding child notes, so no part of the old argument is shortened or blurred. The membership child holds original steps 1 and 2; the restricted-coproduct child holds original step 3.

The parent statement and statement dependencies remain exactly equal to current live. Its three proof steps are unchanged from the retained short assembly, and proof_deps is exactly the union of uses. The two child statements remain unchanged. Each child is unsplit, ready for separate work; the clause extraction is explicitly authorized by this human re-split order.

The previous report is retained in report-before-20261027-restatement.md as historical evidence, including prior worker attribution and all earlier dry-run commits and blocker descriptions. Its claims that child lean fields must survive packaging are superseded by the revised human order. Its claim that the original Lean module is absent is also outdated: the current read clone now has that module. I read it at lines 34-98, checked all standing hypotheses and both declaration signatures, and retained their actual original module in source. The bodies currently visible there contain no literal sorry, but this is not evidence of transitive closure; the explicit released re-split instruction remains in force.

## Lean declarations

- lem-sfb-adic-proper-localizing-membership: AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightDerivedLowerStar_obj (original module Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward, line 47).
- lem-sfb-adic-proper-localizing-restricted-coproducts: AlgebraicGeometry.ProEtale.CondensedRing.ellAdicLocalizingLowerStar_preservesCoproducts (same original module, line 84).

These exact mappings are also in the parent's split_report.lean_declarations. Stage 2 binds them; stage 1 does not relocate Lean declarations or prescribe new modules. The parent retains its maintainer-owned aggregate Lean metadata unchanged.

## Earlier attempts and search provenance

The prescribed abandoned-attempt glob returned no directories. I continued the three retained sandbox nodes, citations and searches.jsonl, and first ran the required dry run before editing; it exited 0 at c089d9cef6f. I compared the live parent and released repair note with the retained work. The current script automatically rebases delivery packaging against the server base; I ran no git command in the shared repository.

All child Mathlib queries and results are those of the prior NH worker in the authentic searches.jsonl (2026-10-27 06:26-06:27 UTC). I read these results and reused them without claiming fresh searches. Each child has grep, LeanSearch, Loogle and LeanFinder records, including both the specific adic statement and more general categorical wording. The membership searches return derived-category, ordinary exact-functor, local-cohomology and adic-completion components, not this geometric hull-membership statement. Restricted-coproduct searches return fully faithful colimit reflection and full-subcategory colimits, not preservation by this actual adic pushforward. No exact match or one-line geometric specialization was found. Unsupported older search claims remain separately preserved in retained-search-claims.json and are not claimed as evidence.

I searched the current permitted Lean trees for the declaration names, the parent blueprint tag and the hull notion. The matching aggregate module lies under Sheaf, not under WeilConjectures; the requested complete project attachment under WeilConjectures was not found. DAG and whole-blueprint duplicate searches from the retained attempt remain applicable because both child statements are unchanged; I also reran blueprint_refs ancestor and a proper/localizing blueprint search. The ancestor tool still returns None because created.item is a historical Lean module identifier. The children retain that computed null ancestor, the parent in via, and the historical blueprint provenance in from.place, as accepted by the earlier dry runs.

## Not duplicates


lem-sfb-adic-proper-localizing-membership vs lem-sfb-adic-proper-localizing-pushforward: requested declaration-sized extraction of membership; the parent additionally defines the restriction and asserts shifts, triangulatedness and coproduct preservation. This clause extraction is explicitly required by the human re-split order.
lem-sfb-adic-proper-localizing-restricted-coproducts vs lem-sfb-adic-proper-localizing-pushforward: requested declaration-sized extraction of restricted coproduct preservation; the parent additionally includes membership and the functor and triangulation structures. This clause extraction is explicitly required by the human re-split order.
lem-sfb-adic-proper-localizing-membership vs det-proper-image-localizing-principle: the latter requires coproduct preservation on the whole ambient category; this child uses preservation only after the source hull inclusion, which is the available theorem.
lem-sfb-adic-proper-localizing-membership vs det-proper-image-localizing-proper: the latter uses the finite-Tor-amplitude Dctf hull; this child uses the exact ordinary bounded-constructible hull and indexed adic certificate of the unchanged parent.
lem-sfb-adic-proper-localizing-membership vs lem-sfb-adic-proper-localizing-coproducts: the existing node asserts ambient-target coproduct preservation on the source hull, not membership in the target hull.
lem-sfb-adic-proper-localizing-restricted-coproducts vs lem-sfb-adic-proper-localizing-coproducts: the existing node's codomain is the ambient derived category; the new node's codomain is the target full hull, and the original proof's colimit reflection is preserved here.
lem-sfb-adic-proper-localizing-restricted-coproducts vs lem-sf-full-subcategory-universe-coproduct-lift: the generic node assumes preservation of all ambient coproducts by F; that hypothesis is not available here. Its full-subcategory inheritance clause agrees with the elementary universal-property calculation but does not prove this geometric theorem.
lem-sfb-adic-proper-localizing-membership vs det-ctf-finite-proper-localizing: the latter concerns finite discrete coefficients and finite Tor amplitude, not the three adic certificate families and exact bounded-constructible hull of the parent.
lem-sfb-adic-proper-localizing-restricted-coproducts vs det-proper-image-localizing-proper: the latter uses the finite-Tor-amplitude hull, rather than the unchanged parent's ordinary bounded-constructible hull.

DAG searches used both requested declaration names, proper/localizing keywords, and the related node statements above; whole-blueprint searches used `localizing`, `proper pushforward`, and `coproduct`. No blueprint node states either exact declaration with this certificate and hull. The ancestor command gives None because the parent created.item is a historical module name rather than a node id. After the first dry-run diagnostic, I set the child ancestor to null as computed by the prescribed ancestor tool, kept the parent in via, and documented the historical lem-sfb-dc-proper-pushforward-left-adjoint-e provenance in source notes and blueprint.from.place. The parent's pre-existing ancestry remains unchanged. The exact current proof paragraph used is specified in source.place and blueprint.from.place.


## Review by NH

I read GOAL, the three-level route rules, the worker and stage-1 contract, delivery-errors B through E, the current released repair order, the chapter and unit records, and literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-cor-existence-ii/sk-cor-existence-ii-restriction.proof.md, part (1). This source uses the identity compactification for proper pushforward on the hulls. The returned proof expands its categorical restriction argument. Each child cites this source and keeps the full expansion as future construction material, not as a completed split.

For the parent, step 1 uses the membership child's final sentence and the hull definition's exact full-subcategory clause. Its object and morphism maps are those of the ambient functor; identities and composition therefore satisfy the same equations. Step 2 uses lem-pc-right-derived-functor-triangulated for natural commutation with integer shifts and distinguished-triangle preservation, and the hull definition for the full triangulated subcategories. The ambient shifts and their inverses are morphisms in the full hulls, with the same naturality and coherence; distinguished triangles are tested by inclusion. Step 3 uses exactly the restricted-coproduct child's conclusion for every index type in universe u+1, including the empty type. I opened each cited statement and checked every citations.json quote verbatim. Thus no parent step uses a cited node's hidden proof or an uncited geometric claim.

For the retained membership construction I opened all five statement-dependency definitions, the generic triangulated right-derived theorem, lem-sfb-dc-lower-star-preserves, and lem-sfb-adic-proper-localizing-coproducts. The generic theorem gives precisely shifts and triangles. The coefficient certificate has exactly the three adic constructors, including specified multiplication; each falls within the bounded-constructible preservation statement. The available coproduct theorem only applies after the source-hull inclusion. Accordingly the retained argument forms P as source hull intersected with the inverse image of the target hull, lifts the discrete coproduct cocone to the full source hull, and uses preservation there. It never assumes preservation on the entire ambient category. Invariance, triangle closure and minimality are exactly the defining hull conditions. The original and expanded texts are both retained in source.note, with their node citations.

For the restricted-coproduct construction, membership supplies the object map, and fullness supplies all morphisms and the equality of composites with the target inclusion. A target full inclusion reflects a colimit by lifting its unique ambient mediating map using fullness and checking its equations and uniqueness using faithfulness. The existing source-hull coproduct theorem is precisely the preservation input for that composite. The inherited shifts and triangles use the ambient theorem, not a different pushforward. This construction remains in source.note, with all original argument text; it is not proof steps on an unsplit node. The generic right-derived theorem is an off-unit tool declared in split_report.tool_uses, rather than a replacement of the unit route.

I checked positive characteristic prime to ell, properness, separated finite type, the identical ordinary module-object derived categories, the absence of a completeness condition, and the u+1 index universe against both child statements and their inputs. Small cases are consistent: identity g gives the same restriction; K=0 and empty source give zero; empty index type gives the initial/zero cocone; singleton gives the identity comparison. No finite Tor-amplitude, algebraic-closure or stronger ambient coproduct hypothesis is added. Both statements introduce all their objects and cite definitions, and child dependencies are one-way, with no mathematical edge back to the parent. The parent's three assembly steps are each below 2000 characters and total below 3000; all longer construction material is preserved in the explicitly requested source notes. No new hidden proof step is asserted as elementary. The report's duplicate comparisons explain why the two human-required declaration items are distinct from the existing generic and finite-Tor-amplitude results.

The previous attempts' blocking conclusion is repaired by the newly authorized split_report allocation path, without changing any launcher or repository tool. The only remaining downstream work is to split and prove the two unsplit children and bind their Lean declarations in the appropriate stage.

## Validation and delivery

Initial required dry run on the retained sandbox: exit 0, c089d9cef6f. Final dry run and push are recorded after completion.
