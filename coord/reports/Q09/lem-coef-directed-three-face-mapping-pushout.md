# Stage-1 report: lem-coef-directed-three-face-mapping-pushout

## Files written

- `dag/nodes/sec-six-functors/lem-coef-directed-three-face-mapping-pushout.json`: statement unchanged; nine-step split of the actual three-face union, including the specified maps and naturality. No Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-directed-enriched-amalgamation.json`: new statement-only lemma for one directed enriched gluing along a homotopically full middle block; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-triangular-bar-excision.json`: new statement-only lemma for the derived coend over a category with two directed blocks; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-extreme-bimodule-attachment.json`: new statement-only lemma for changing the extreme mapping bimodule of a directed category; no Mathlib match.
- `citations.json`: verbatim statements for every node cited by each numbered proof step.

The sandbox also retains its original `searches.jsonl` and construction script. The resumed turn preserved the earlier split and searches; it did not rerun the construction script or invent search records. There are three new nodes and zero Mathlib leaves.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item tag and directed gluing/bar/attachment vocabulary found no declaration stating these assertions. Upstream master sorry declarations are not treated as finished proofs.

## Sources wanted

WANTED: archived Higher Topos Theory, Sections 2.2.2 and 2.2.4 and Appendix A.3.2–A.3.3, for the item and all three new nodes. The item and the three new assertions are agent-formulated, not numbered theorems quoted from HTT; the appendix is background for their terminology, not a claim that it states these formulas. Online PDF retrieval during the resumed turn failed (timeout/inaccessible host and then provider HTTP 429). No document was downloaded.

I read the local `main-20261015` statement and proof of `prop-coef-integral-exceptional-adjoint`, the recorded chapter and unit, and the statements of all cited DAG nodes. The ancestry supports the inherited coherent middle-adjunction foundation. The current blueprint paragraph itself proves the integral exceptional adjunction by finite reductions and derived coefficient adjunction, and does not state this three-face calculation. The report therefore does not attribute the new gluing lemmas to that paragraph as quoted theorems. The proof is explicitly agent-written below that ancestor; no chapter or unit route is replaced and no unit record is changed. No SGA source is used.

## Problems found and corrections

The inherited item was unsplit. Its distinction between derived composition through an inverted full-edge comparison and a nonexistent strict triangle retraction is essential and is preserved. The formula is a homotopy pushout, not a pushout of components. I kept its hypotheses, conclusion, and statement dependencies unchanged.

On resumption I found a citation gap in step 2: the generic projective-diagram theorem assumes a combinatorial model category, whereas the cited coherent-nerve statement does not explicitly give that adjective for Bergner categories. I replaced that input by `lem-coef-simplicial-derived-pushout-mapping`, whose statement explicitly supplies a cofibrant span replacement in Bergner categories. Clause (b) of the existing cofibrant colimit comparison now applies to six cofibrant objects with the required cofibration legs, without a properness assumption. Citations and the dependency union were regenerated after this correction.

## Not duplicates

lem-coef-directed-enriched-amalgamation vs lem-coef-simplicial-derived-pushout-mapping: the existing node calculates the homotopy function complex of functors from a category pushout to a target; the new node calculates internal mapping spaces between specified source and target objects using directed overlap modules.

lem-coef-directed-enriched-amalgamation vs lem-coef-infinity-fiber-colimit-collage: the existing node extends diagrams on ordinary Grothendieck-construction fibers to a collage; it does not calculate an enriched amalgamation or its derived mapping module.

lem-coef-triangular-bar-excision vs lem-coef-derived-space-module-coyoneda: the existing node gives the bar model, homotopy invariance, representable contraction and Fubini; it gives no decomposition over two blocks. The new node gives that decomposition with both action maps.

lem-coef-extreme-bimodule-attachment vs lem-coef-scat-bergner-left-proper-pushouts: the existing node concerns a Dwyer–Kan equivalence on every mapping space pushed along a cofibration; here the exceptional extreme mapping spaces need not be equivalences, and their resulting square is calculated.

lem-coef-extreme-bimodule-attachment vs lem-coef-simplicial-derived-pushout-mapping: the existing node concerns outgoing homotopy function complexes, not evaluation at an ordered extreme pair and invariance at every other pair.

All three new nodes vs lem-coef-directed-three-face-mapping-pushout: none states a clause for a three-horn or the item's three-face formula. They address respectively one amalgamation, a two-block module calculation, and one extreme attachment. Steps 1–9 carry the horn decomposition, overlap verification, identification of P, Q, R, D, pushout pasting, actual inclusion maps and naturality.

The whole-DAG keyword search and `tools/blueprint_refs.py search` for directed, coend, and bimodule found no blueprint node with any of the three statements. The bimodule blueprint hits concern ordinary monoidal module objects, not enriched derived bars. Their ancestor is `prop-coef-integral-exceptional-adjoint` with the inherited via chain, and the precise supporting gluing place is recorded. No Stacks tag states these enriched homotopy-theoretic assertions; none is fabricated as a citation.

## Review by Q09

I checked the files against delivery-errors B–E, including the substantive hypotheses rather than only JSON shape. Each new node introduces all object sets, categories, functors, directions, module variances and smallness. Each is unsplit with an empty proof and empty proof dependencies. The missing archival source is disclosed above. The agent assertions can be understood independently: amalgamation is the derived composition over its overlap; excision separates constant-block bar strings from strings crossing once; extreme attachment cannot propagate to another label pair because a word can contain an extreme arrow only once, with all its prefix and suffix inside the two endpoint blocks. Equivalence of the endpoint categories is necessary for evaluating that module pushout at the original endpoints and is explicitly assumed in the attachment node.

Step 1 uses the right-pinched simplex definition in `def-cbc-enhanced-diagrams-cones` and the natural p and theta comparisons in `lem-coef-pinched-rigidification-resolution`. A pinched simplex has all initial labels i and last label j, so factors through the edge ij. Both edge and triangle inverse images are quasicategories by the item hypothesis. Naturality gives the actual inclusion comparison; two-out-of-three gives the result. This does not assert such a result for the whole K, which need not be a quasicategory.

Step 2 uses the explicit subset-poset rigidification and left Quillen adjunction in `lem-coef-coherent-nerve-comparison`: all simplicial sets are Joyal-cofibrant and inclusions are cofibrations. The equations for U, W, and their intersections are degreewise inverse-image identities. `lem-coef-simplicial-derived-pushout-mapping` supplies the replacement span and `lem-coef-model-cofibrant-colimit-comparison` (b) identifies its colimit with the strict one. Thus the maps are the actual inclusion cocones. This is the citation repaired on resumption.

Step 3 uses the Dwyer–Kan change-of-index Quillen equivalence in `lem-coef-simplicial-projective-model-calculus`, the Kan model of `lem-coef-kan-quillen-right-proper`, and the defining action quotient of `def-coef-enriched-coend`. The coend/left-Kan-extension identity imposes the same action relations on both sides. Deriving it and using the unit and counit gives change of base. `lem-coef-derived-space-module-coyoneda` explicitly supplies module invariance, Fubini, retained outer variables and composition compatibility. There is no strict inverse to an edge inclusion.

Step 4 invokes exactly the new amalgamation statement with overlap 12, incoming block 0 and outgoing block 3. Step 1 supplies fullness on all overlap pairs, including pairs within fibers; step 2 supplies absence of backwards arrows. The new node supplies both invariance of the old triangle mapping sets and the displayed new coend, with its composition map.

Step 5 invokes the new triangular excision statement on the two blocks of C[K_12]. Its first action is on Y and gives composition in 123; its second is on X and gives composition in 012. The cited coend and pinched-comparison nodes justify replacing the restrictions by the actual M_ij and A_i. The resulting mixed term is exactly R and the outside terms are P and Q, with the specified maps.

Step 6 invokes amalgamation on 02 and 23, now with middle block 2, and uses its composition/naturality clause and the coend augmentation clause to identify both images of Q. The edge-to-023 comparison is available from the pinched node because K_023 is quasicategorical. This verifies maps as well as the homotopy types.

Step 7 checks every hypothesis of the new extreme attachment node for T=C[W], V=C[K_023], B'=C[U], I={0,1,2,3}, S={0,2,3}. The map T to V is a weak equivalence outside the extreme pair by steps 1 and 6, including empty decreasing mapping sets. The map T to B' is a weak equivalence within both endpoint blocks by steps 4 and 6. Object functions are the actual inclusions. The node then gives the pointwise pushout and all other mapping comparisons; it is not used for a stronger arbitrary attachment claim.

Step 8 writes the pushout-pasting universal property, eliminating the intermediate Q map together with its specified homotopy, not merely a componentwise equality. The preceding steps identify the composite R to D as composition first in 012 and then in 023. Inverting the actual 03-to-023 full-edge map retains the actual 03 inclusion in the final cocone.

Step 9 obtains each non-extreme edge-to-K comparison by a triangle in U and the amalgamation and attachment conclusions. For any other face containing the pair, its edge map is an equivalence by step 1, so two-out-of-three proves the actual face-to-K map. This also covers equal labels. Inverse images of fixed faces, composition pairings, and the stated natural module comparisons all commute with maps over H; no lift selection is made.

I tested the new statements on empty blocks, empty mapping spaces, discrete categories with singleton blocks, and nontrivial endomorphism blocks. Empty overlap gives a disjoint union and empty new cross mapping set. With one middle object and trivial endomorphisms the amalgamation gives the product of the two mapping spaces. For triangular excision with T the interval and constant point modules, the diagram is point <- point -> point and gives a point, as does its contractible bar; with empty off-diagonal N it becomes the coproduct of the two separate bars. For extreme attachment with only two endpoint blocks the assertion reduces to a pushout of bimodules over endpoint categories; if f is everywhere an equivalence it reduces to invariance. With intervening blocks, direction forbids any prefix before the least block or suffix after the greatest block; it cannot add another mapping pair. These tests also explain why the endpoint equivalence assumption is present.

I read the recorded Mathlib search results rather than repeating the same questions. The returned ordinary coend definitions (End.lean:45–79), simplicial-category enriched hom definitions (Basic.lean:49–72), simplicial nerve background (SimplicialNerve.lean:28–32), and horn gluing (HornColimits.lean:338–424) do not state these derived enriched formulas. Each new node has the actual logged LeanFinder, Loogle, grep and LeanSearch queries, including a second natural-language phrasing; the invalid original Loogle identifier is recorded as invalid, not as evidence of absence. No new node is claimed as a Mathlib leaf. All nine proof steps are below 2000 characters; none hides a long inline sublemma. The report records the general enriched lemmas as separate statement-only nodes rather than hiding them in the item.

## Unfinished work

No part of this item's one-level split is deferred. The three new nodes intentionally remain statement-only stage-1 work, as required. Their archival references are wanted; this delivery does not claim to have proved their statements in Lean or independently split them.
