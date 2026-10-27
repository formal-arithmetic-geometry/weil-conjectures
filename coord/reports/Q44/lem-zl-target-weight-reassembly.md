# Stage-1 report: lem-zl-target-weight-reassembly

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-target-weight-reassembly.json`: statement node, now split into four steps; no Mathlib match.
- `citations.json`: one exact quotation of the cited statement for each of the seven step/node citations.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The item statement and its statement dependencies are unchanged. The imported searches were retained; five searches actually run for Q44 were appended. Their exact tools and queries are in `searches.jsonl`.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, reassembly, and `of_openClosed`, and read `DeligneLaumon/Reduction/FormalSteps.lean:337` and `:360`. The complex theorem has a proof without a literal sorry, but `WeilSheaf/Category.lean:173` defines its `WeilComplex` as a full subcategory of the derived category of pro-etale Weil sheaves. The item explicitly uses fixed pairs over the common-stage coefficient category. These are different constructions; the item's definition even explains the point/Jordan-block distinction. An attachment would silently identify the two categories. I therefore use the existing natural-language fixed-pair interfaces instead. The sheaf theorem alone does not state the complex clause.

## WANTED

None: the source used for this split is present in the current blueprint. This proof follows that agent-written source, so `proof_origin.by` is `agent`, not `document`.

## Findings and changes

The item was unsplit, with no proof steps, and there was no earlier sandbox attempt. I read its chapter and unit and followed the target reassembly portion of the unit's open-closed argument. The source is `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-excision/lem-zl-morphism-open-closed-reduction.proof.md`, Part 2. Its target argument first bounds extension by zero and closed pushforward, then invokes open-closed devissage, then specializes to a sheaf in degree zero. Here the first two functor bounds are hypotheses of the item, so reproving finite pushforward or preservation by extension by zero would be unnecessary.

I read the current blueprint statement and proof of `lem-zl-open-closed-weight` as well. This existing node supplies exactly the outer-term criterion; no new reassembly lemma is created. The current source and the item's statement agree. There is no statement dispute, source correction, or change of the unit's route.

The whole-DAG searches for mixed-weight restrictions, extension/triangle weights and reassembly, and blueprint searches for `reassembly`, `outer terms`, `localization triangle`, and `extension weight`, found the already-existing outer-term lemma. The item itself assumes bounds on the unpushed restrictions and functor preservation; the outer-term lemma assumes bounds on the already pushed objects. Thus the latter is the tool used in the proof, not a second copy to create. `blueprint.same_as` remains empty: no blueprint node states this item's full conditional statement and sheaf clause verbatim or in an equivalent form without those preservation assumptions.

The recorded Mathlib searches used LeanFinder in two phrasings, Loogle, grep, and LeanSearch through the prescribed wrapper. Loogle and grep returned no hits. LeanFinder returned polynomial constructible-set bounds, scheme-localization facts, and derived cohomological bounds; LeanSearch returned topological gluing, order upper bounds, Selberg and Lie weights. None states Frobenius mixed weights or this reassembly result. The generic derived t-structure facts do not turn the item into a one-line Mathlib specialization.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Existing nodes are cited instead of duplicated. No Stacks tag is introduced: the source is this blueprint's formal argument, and all non-elementary geometric inputs are existing nodes.

## Review by Q44

I checked the item against Part 2 of the current blueprint proof, and read the complete statements of all seven cited nodes. There are no new-node sources to review.

Step 1 uses only the item's hypotheses: evaluating the two assumed inclusions on the two restrictions gives bounds on precisely the two pushed objects, with the same real number u. It does not use finite-pushforward preservation or any unstated exactness. This is an elementary instantiation of the assumptions.

Step 2 uses `prop-sf-open-closed-triangle-all-stages` for its displayed localization triangle and its final Weil-equivariance clause, and `lem-zl-open-closed-weight` for its explicitly stated outer-term criterion. The scheme Y is separated of finite type over k; the two immersions are complementary and descend to k_0; Qbar_l is an allowed coefficient stage. The triangle's outer terms are exactly A and B from step 1. I explicitly state that the underlying triangle is distinguished and its arrows are equivariant; no triangulated structure is imposed on the category of fixed pairs. I do not use a proof-internal construction of either cited node.

Step 3 uses `lem-a1-constructible-pullback-t-exact` for the exact functor on the common-stage constructible hearts. Both base-changed immersion maps are between finite-type k-schemes, so its hypotheses hold. It uses `def-weil-constructible-heart` for the heart, and `prop-constructible-truncations` for standard cohomology and its compatibility with automorphism pullback. Thus a heart object has only its degree-zero cohomology, with the expected Weil structure. It then expands `def-weil-complex-weights` and `def-weil-punctual-weights`: degree zero has bound u, and the other degrees are zero and admit the length-zero mixed filtration for any u+n. This checks every degree, including negative ones. These are the exact statements quoted in `citations.json`, not purported facts extracted from their proofs.

Step 4 applies the already proved complex case to the heart object G, then uses the degree-zero equivalence established in step 3. It introduces no extra geometric fact or lemma. The statement explicitly places G and its restrictions in degree zero, and t-exactness justifies that convention for the derived restrictions. The two generic cohomological tools are declared in `split_report.tool_uses`; they provide coefficient infrastructure, not an alternative direct-image weight route.

I checked the B--E return cases individually: no new nodes or hidden new definitions; no unrun searches recorded; no sources cited for meaning instead of actual statements; no new tags; no theorem used beyond its hypotheses; no use of a node's proof instead of its statement; no relabelled copy of a clause; no cycle introduced by calling the item from a child; and no unsupported comparison between coefficient categories. The only substantial attachment issue found was repaired by declining the category-mismatched Lean candidate. All proof steps are shorter than 2000 characters.

Small cases checked: M=0 and G=0, any real u including negative u, V_0 empty, T_0 empty, and Y_0 empty. The assumptions still give both outer bounds; the zero sheaf's empty filtration handles zero terms without choosing an impossible weight. When one piece is empty, the other is the whole scheme and the argument specializes to the corresponding restriction. No nonemptiness, smoothness, purity, or properness hypothesis is used.

## Unfinished work

None for this one-level split. Dependencies retain their existing statuses; no Lean was written or compiled. The required server preflight is run through the delivery tool before pushing.
