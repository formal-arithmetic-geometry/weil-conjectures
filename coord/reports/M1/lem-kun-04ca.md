Files written:

- `dag/nodes/sec-smooth-purity/lem-kun-04ca.json`: statement, split proof, blueprint metadata, and seven Mathlib/search records; no new nodes.
- `citations.json`: verbatim citations for every proof dependency.

Attachments: none.

WANTED: none.

The imported proof was incomplete: it omitted the support and scheme-convention dependencies, and it used the inverse-image stalk identification without citing a node. It also incorrectly said that an étale neighbourhood of a closed subscheme extends by composing with the closed immersion; that composite is not generally étale. I replaced that claim by the initiality statement already supplied by `lemma-openclosed-stalk-lowerstar`, and cited the existing `lem-weil-pbc-inverse-image-stalk-germ` node for the inverse-image stalk comparison. No new node was needed because all non-elementary facts are already stated in existing nodes.

## Review by M1

I checked the item against its blueprint proof paragraph and the definitions in `def-weil-pbc-direct-image`, `def-weil-pbc-inverse-image`, `def-kun-support`, and `def-weil-pbc-scheme-conventions`. The first part uses the direct-image formula and the statement of `prop-openclosed-lowerstar-fully-faithful`, which explicitly says that the closed-immersion pushforward is fully faithful and its counit is an isomorphism. For the essential-image part, I read `lemma-openclosed-stalk-lowerstar` (initiality and the stalk formula), `lem-weil-pbc-inverse-image-stalk-germ` (inverse-image stalks identify with the original stalks), `def-kun-support` (support is defined by nonzero geometric stalks), `def-weil-pbc-geometric-stalks` (stalks as filtered colimits over pointed étale neighbourhoods), and `lemma-weil-pbc-geometric-stalk-conservative` (stalkwise isomorphisms are global isomorphisms). At points of Z the unit is the identity under the two cited stalk comparisons; outside Z the open complement supplies a cofinal system with empty fibre product, while the support hypothesis makes the original stalk zero. I verified each citation quote in `citations.json` is copied verbatim from the cited node. The only off-unit citation is the generic inverse-image stalk comparison, declared as a tool use in `split_report`; no hypotheses beyond the stated closed immersion and geometric points are added. The Mathlib searches were run for both the concept and a second phrasing; they found only unrelated scheme/module declarations, with LeanSearch unavailable, so the item is not a Mathlib leaf.

What I corrected: the proof now cites all facts it uses, removes the false étale-composition parenthetical, includes the missing conservativity/support dependencies, and changes status from imported to split.

## Second reading by M1

- Item statement: checked hypothesis by hypothesis against Stacks Proposition Tag 04CA, label `proposition-closed-immersion-pushforward`; verdict: agrees for schemes, abelian étale sheaves, full faithfulness, left inverse, and support characterization.
- Step 1: checked the direct-image formula against `def-weil-pbc-direct-image`, the adjunction/counit against `prop-openclosed-lowerstar-fully-faithful`, the stalk maps against `lemma-openclosed-stalk-lowerstar` and `lem-weil-pbc-inverse-image-stalk-germ`, support vanishing against `def-kun-support`, and global detection against `lemma-weil-pbc-geometric-stalk-conservative`; verdict: every non-elementary fact is cited and the stalk argument is valid.
- New nodes: none; no new-node statements require review. Existing dependency statements were opened and their quoted citations checked verbatim.
- Edge cases: checked $Z=X$ (unit is the identity), $Z=\varnothing$ (both sides vanish off the empty support), and the zero sheaf; verdict: consistent.
- Changes made: replaced the imported blueprint source with Stacks Tag 04CA and documented the second reading; no mathematical statement or proof text was changed beyond the worker's repair.

