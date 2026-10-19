# Stage-1 worker report

1. Files written:
   - `dag/nodes/sec-six-functors/lem-coef-localization-monomorphic-pushout.json`: item, split; statement unchanged; no Mathlib match.
   - `dag/nodes/sec-six-functors/lem-coef-categorical-pushout-mono.json`: one new statement-only helper; no Mathlib match.
   - `citations.json`: verbatim quotations for every cited node in every proof step.

2. Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, Kerodon tags and localization/pushout terms; no project declaration states this item. The source checkout and upstream master are reference only and contain no finished declaration to attach.

3. WANTED:
   - archived Kerodon Proposition 6.3.5.3 (01N7), implication (1) to (2), for the item;
   - archived Kerodon Example 4.5.5.12 (01FJ), for the new categorical-pushout helper.
   These sources were read online on 2026-10-17 and are recorded as online sources in the nodes.

4. What I checked and corrected: the imported item was statement-only, so I supplied its three-step proof. The proof first obtains the two categorical pushout squares from the new helper, then forms the full subcategories of component functors inverting the specified edge collections and transports the three component equivalences through the homotopy-pullback comparison, and finally identifies the resulting full subcategory with functors inverting the union of the two image collections. I did not cite `lem-coef-universal-localization-pushout`, because that node is a stronger universal-base-change statement and depends on this item, so it would create a cycle. The maps `p_i` and the non-monomorphic legs are used exactly as in 01N7; only `u_0` and `v_0` are required to be injective. The helper is strictly smaller than the item: it gives categorical pushout/functor pullback structure without any localization maps or edge collections.

5. What remains: the helper is intentionally unsplit for a later worker. No Lean was written, compiled, or searched through compiler tools. No shared repository file was changed.

## Review by NB

I read the complete item source, Kerodon Proposition 6.3.5.3 (01N7), including hypotheses (a)--(d), the two categorical pushout faces, the three component localization collections, their compatibility inclusions, and the equivalence of (1) with (2). I also read Example 4.5.5.12 (01FJ), which supplies categorical pushouts for simplicial-set pushout squares whose indicated leg is a monomorphism. The item's statement has exactly those hypotheses after renaming the corners: `u_0` and `v_0` are the two monomorphic legs; `u_1`, `v_1`, and all `p_i` remain arbitrary; and the conclusion uses precisely the images `j_0(V_0) ∪ j_1(V_1)`.

For Step 1, I checked the new helper's statement against 01FJ and the categorical-pushout functor characterization. Its statement explicitly says what the item takes from it: both pushout squares induce pullback squares of coherent functor quasicategories, with no quasicategory assumption on the simplicial inputs. The enhanced-diagram definition supplies the functor-category, core and homotopy-pullback conventions.

For Step 2, I checked each `p_i` hypothesis against the localization definition: precomposition is an equivalence onto the full subcategory of functors carrying `V_i` to equivalences. The two inclusions of edge collections make the restriction cospan preserve these full subcategories. The cited terminal-pullback criterion explicitly states invariance under equivalences of cospan diagrams, which is the only comparison used to pass from the three component equivalences and the Step 1 pullback to the pullback of the `L_i`.

For Step 3, I checked the edge bookkeeping in both directions. A functor on `X` inverting `j_0(V_0) ∪ j_1(V_1)` restricts to the two `L_i`; conversely the two restrictions invert every generator in the union. Since the subcategories are full, this vertex condition identifies the entire coherent subcategory, including transformations and higher simplices. The definition node then supplies exactly the final localization universal property for every quasicategory target.

I tested the helper and item on empty overlap, empty simplicial sets, identity vertical maps, disjoint pushouts, a point target, and a noninjective second span leg. These cases preserve the stated edge union and require no hidden nonemptiness or quasicategory assumption. The helper's Mathlib searches were run with LeanFinder, Loogle, grep and LeanSearch; the returned declarations concern ordinary set pushouts, monomorphism cobase change, horns, or adhesive categories and do not match coherent categorical pushouts. The item's prior recorded searches were retained. No SGA source or off-unit theorem is used.

## Not duplicates

lem-coef-categorical-pushout-mono vs lem-coef-universal-localization-pushout: the helper states categorical pushout/functor pullback for one arbitrary simplicial span with one monomorphic leg; the existing node assumes three universally localizing vertical maps and concludes universal localization of a two-span map. The existing node also depends on the item, so it cannot replace the helper.

lem-coef-categorical-pushout-mono vs lem-coef-infinity-functor-pushout: the helper applies to arbitrary simplicial sets and degreewise pushouts, while the existing node assumes a pushout already formed in `Cat_infty` of quasicategories and states a whole functor-category formula there.

lem-coef-categorical-pushout-mono vs lem-coef-localization-monomorphic-pushout: the helper is the categorical-pushout universal property for one arbitrary simplicial span; the existing node is the specified-edge localization gluing theorem for two spans and three localization maps, and its proof uses the helper-level fact rather than stating it.
lem-coef-categorical-pushout-mono vs lem-pc-cech-differential-repeated-decomposition: both cite the numeral 01FJ, but the existing node is a Stacks Cech differential decomposition, whereas the helper is Kerodon's categorical pushout of simplicial sets along a monomorphism.
lem-coef-categorical-pushout-mono vs lem-pc-signed-cech-extension-differential: both cite the numeral 01FJ, but the existing node is a Stacks signed Cech extension calculation, whereas the helper is Kerodon's categorical pushout universal property.
lem-coef-categorical-pushout-mono vs def-pc-ordered-cech-module-coordinates: both cite the numeral 01FJ, but the existing node defines ordered Cech module coordinates, whereas the helper concerns coherent functor categories of simplicial pushouts.
lem-coef-categorical-pushout-mono vs lem-pc-alternating-cech-restriction-homotopy: both cite the numeral 01FJ, but the existing node proves an alternating Cech restriction homotopy, whereas the helper proves categorical pushout for simplicial sets.
lem-coef-categorical-pushout-mono vs lem-sc-principal-open-subset-cech-comparison: both cite the numeral 01FJ, but the existing node compares principal-open Cech complexes, whereas the helper is the Kerodon pushout theorem.
lem-coef-categorical-pushout-mono vs lem-pc-cech-differential-repeated-cancellation: both cite the numeral 01FJ, but the existing node concerns repeated Cech cancellations, whereas the helper concerns categorical pushouts and functor pullbacks.
lem-coef-categorical-pushout-mono vs lem-pc-ordered-cech-module-retraction: both cite the numeral 01FJ, but the existing node constructs an ordered Cech module retraction, whereas the helper concerns arbitrary simplicial-set spans.
lem-coef-categorical-pushout-mono vs lem-pc-ordered-cech-module-signed-section: both cite the numeral 01FJ, but the existing node constructs a signed Cech section, whereas the helper is a categorical pushout statement.
lem-coef-categorical-pushout-mono vs lem-pc-alternating-cech-section: both cite the numeral 01FJ, but the existing node constructs an alternating Cech section, whereas the helper identifies coherent functor pullbacks for simplicial pushouts.
lem-coef-categorical-pushout-mono vs lem-pc-ordered-cech-module-restriction-map: both cite the numeral 01FJ, but the existing node is a Cech restriction map, whereas the helper is Kerodon's monomorphic simplicial pushout theorem.
lem-coef-categorical-pushout-mono vs lem-pc-cech-differential-repeated: both cite the numeral 01FJ, but the existing node is a repeated Cech differential statement, whereas the helper is a categorical pushout/functor-category statement.


## Second reading by NB

- Step 1: checked against Kerodon Proposition 6.3.5.3 (01N7), hypotheses (a), and Example 4.5.5.12 (01FJ); the two stated degreewise-injective legs give exactly the two categorical pushout squares, and the helper supplies the coherent functor pullbacks. Verdict: sound.
- Step 2: checked against 01N7, the definition [def-coef-universally-localizing-simplicial-map], and [lem-coef-infinity-terminal-pullback-criterion]; the edge inclusions preserve the three full subcategories and the cited invariance statement supplies the homotopy-pullback comparison. Verdict: sound.
- Step 3: checked against the final edge-union argument in 01N7 and both cited node statements; restriction and the converse edge check identify the full subcategory on the union, including coherent transformations. Verdict: sound.
- New node `lem-coef-categorical-pushout-mono`: checked against Kerodon Example 4.5.5.12 (01FJ) and the categorical-pushout definition; it is self-contained, has the required enhanced-diagram dependency, and is strictly smaller than the item. Verdict: sound and needed.
- Item statement: checked hypothesis by hypothesis against 01N7; the span map, the two monomorphic legs, the three localization collections, compatibility inclusions, pushouts, and image union all match. Empty overlap, empty simplicial sets, identity vertical maps, disjoint pushouts, a point target, and a noninjective second leg preserve the statement. Verdict: sound.
- Mathlib audit: independent LeanFinder, Loogle, and grep searches found only ordinary simplicial-set pushouts, monomorphism cobase change, or ring localization; no exact coherent localization theorem. The malformed Loogle query was recorded as zero hits by the search tool, and the existing valid searches remain in the node records.
- Changes: no item or node mathematics required repair. I appended this independent reading, retained the worker's source and WANTED entries, and removed only the temporary `Test.lean` generated by the search command.
