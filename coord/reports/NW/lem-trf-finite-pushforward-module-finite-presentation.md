# NW: lem-trf-finite-pushforward-module-finite-presentation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-pushforward-module-finite-presentation.json`: statement; split into six steps, both neighbourhood and stalk assertions retained; no Mathlib match found.
- `dag/nodes/sec-trace-formula/lem-trf-finite-singleton-fibre-stalk-ring.json`: new statement-only, unsplit; the finite local-ring map and its finite-presentation refinement in Stacks 05B8(2–3); no Mathlib match found.
- `citations.json`: a verbatim statement witness for each node cited in each proof step.
- `report.md`: this report. Search results are retained in `searches.jsonl` and recorded verbatim in the node search records.

## Attachments

None. I searched the project source for the item id, its blueprint docstring tag, finite pushforward finite presentation, and singleton-fibre stalk statements. The declarations in `WeilConjectures/Modules/FinitePushforward.lean` concerning the structure sheaf over a locally Noetherian target or finite locally free pushforwards do not assert the item: the item has arbitrary quasi-coherent modules, no Noetherian hypothesis, and two separate equivalences. No exact project declaration was found for the new local-ring lemma either. No Lean files were changed or compiled.

## WANTED

None: all mathematical sources used are already in the supplied literature.

## Corrections and route

The mathematical statement was correct. Its imported references were not: Descent 03C4 is faithfully flat descent of finite presentation, whereas the finite ring-extension comparison needed here is Descent 05B4, `lemma-finite-finitely-presented-module`. More on Morphisms 0A1H is unrelated; the singleton-fibre statement is 05B8, `lemma-finite-morphism-single-point-in-fibre`. I corrected these references. I made the existing Zariski direct-image notation and its scalar action explicit and cited the module-stalk definition; this adds no hypothesis and changes neither equivalence.

I read the current chapter and unit and the blueprint ancestor `lem-trf-local-term-locality`. This auxiliary item belongs to the already-recorded elementary-devissage/flatification ancestry of that node, rather than being a new replacement for the unit's contracted-correspondence argument. I completed the `blueprint.from.via` chain through `created.item`, kept the existing chapter and unit, and searched the whole blueprint for the module comparison and singleton-fibre ring statement. No alternate blueprint node states either. The item is not a unit key, so no unit record was written. The generic affine quasi-coherent tools from the proper-base-change unit are declared in `split_report.tool_uses`; the essential finite-extension module comparison already belongs to this trace-formula unit. No SGA route is used.

## What remains unfinished

Nothing in the item's split. The one new node intentionally remains statement-only as the stage-1 one-level rule requires. Its proof is not assumed to be in Lean. The existing finite-extension module lemma remains an independently queued dependency and was not modified.

## Not duplicates

lem-trf-finite-singleton-fibre-stalk-ring vs lem-trf-finite-singleton-fibre-localization: the existing node states 05B8(1) and (4), namely cofinal neighbourhoods and the arbitrary quasi-coherent pushforward-stalk isomorphism. The new node states only 05B8(2) and (3), namely a finite local-ring map, and a finitely presented algebra map when the morphism is finitely presented. Neither finiteness nor algebra finite presentation of that ring map is asserted by the existing node. The item proves the two elementary topological/germ arguments explicitly and creates no nodes for them.

lem-trf-finite-singleton-fibre-stalk-ring vs lem-trf-finite-pushforward-module-finite-presentation: both now reference 05B8, but the new node concerns finiteness and algebra finite presentation of a local-ring homomorphism; the item concerns finite presentation of arbitrary quasi-coherent modules and two equivalences. The new node asserts neither equivalence or any sheaf finite-presentation clause.

lem-trf-finite-singleton-fibre-stalk-ring vs lem-trf-finite-extension-module-finite-presentation: the existing node assumes a finite finitely presented ring map and compares module finite presentation; the new node supplies those ring-map hypotheses from the singleton scheme fibre and does not compare modules.

lem-trf-finite-singleton-fibre-stalk-ring vs lem-sbc-finite-presentation-stalk-localization-model: the latter supplies an essentially finitely presented model of a stalk map for a locally finitely presented morphism, not a finite ring map or an actually finitely presented algebra under the singleton-fibre hypothesis.

lem-trf-finite-singleton-fibre-stalk-ring vs lem-sc-affine-pushforward-stalk-localization: the latter describes localization of the affine structure-sheaf pushforward at a base prime; it does not identify the source local ring at the unique fibre point or assert its finiteness and finite presentation over the target local ring.

The first dry run detected the newly synced `lem-trf-finite-singleton-fibre-localization`; I then opened its full statement and source reference and checked the distinction above. My earlier searches had not returned it. I searched the whole DAG by the exact 05B8 tag and by finite morphism, singleton fibre, local ring, stalk localization, and finite presentation, and searched the project source and whole blueprint before creating the new node. The other 05B8 content used here (shrinking and germ comparison) is explicitly proved in the item's elementary steps rather than duplicated as nodes.

## Repair of returned delivery

The landing review reported that `lem-trf-finite-extension-module-finite-presentation` had changed since the reviewed delivery. I re-read its current DAG statement: it now spells out the hypotheses as finite generation of $S$ as an $R$-module and finite presentation of $S$ as an $R$-algebra. I updated Steps 3 and 6 to use those exact hypotheses and replaced both citation witnesses in `citations.json` with the current statement verbatim. The cited node still supplies both directions for arbitrary $S$-modules, so no route or mathematical conclusion changed.

## Review by NW

I read Stacks `flat.tex`, Tag 057T (`lemma-devissage-finite-presentation`), including the neighbourhood comparison of conditions (2) and (3) and the final stalk comparison. I also read the complete finite-pushforward argument in `descent.tex`, Tag 05B4; the ring-module comparison in `algebra.tex`, Tag 0564; and the affine quasi-coherent finite-presentation criterion in `properties.tex`, Tag 01PC. For the new node I read all four parts and the proof of `more-morphisms.tex`, Tag 05B8, and the cited unique-prime localization lemma in `algebra.tex`, Tag 00EA. Thus the item and the new node have separate, directly checked sources, not inferred tag titles.

For Step 1 I opened `lem-weil-pbc-finite-closed-map-finite-fibres` and checked that its statement really says images of every closed subset are closed, not merely that fibres are finite. I opened `lem-weil-pbc-affine-opens-basis` and checked it gives an affine open inside any given open neighbourhood. The complement argument uses the entire fibre being the single point, so no image of the closed complement can contain u. This proves the required cofinality and is an explicit elementary argument, not an uncited cofinality theorem.

For Step 2 I opened `def-weil-finite-integral-morphism`: it gives both the affine inverse image and the finite section-ring map. I opened `lem-weil-pbc-lfp-affine-opens-finite-presentation`: it applies to any such pair of affine opens, so the assumed finite presentation of p supplies its locally-finite-presentation hypothesis and hence an actual finitely presented R-algebra S. I opened `lem-weil-pbc-affine-pushforward-base-change` and use only clause (1), which states quasi-coherence of the affine direct image. I opened `lem-weil-pbc-pushforward-spec-global-sections`; its natural identification includes restriction of scalars along R to S, not just an abstract additive-group identification. No base-change assertion is used.

For Step 3 I opened `lem-weil-pbc-quasi-coherent-finite-type-affine` and checked clause (b), rather than its finite-type clause: it gives precisely finite presentation of the sheaf if and only if finite presentation of its section module. Both sheaves are quasi-coherent by the assumptions and Step 2, and both opens are affine. I opened `lem-trf-finite-extension-module-finite-presentation`; its statement has both directions for any S-module, provided R to S is finite and finitely presented as an algebra. Step 2 supplies both hypotheses. This avoids replacing finite presentation by finite generation or silently requiring a Noetherian base.

For Step 4 I opened `def-weil-pbc-module-finite-type-presentation` and checked the finite-free local presentation definition. Such presentations restrict to smaller open subsets, which is the only additional fact used. Applying Steps 1 and 3 proves each direction on an actual neighbourhood. This step does not deduce neighbourhood finite presentation from finite presentation of a single stalk.

For Step 5 I opened `def-weil-pbc-module-stalk` and checked its representative, equality-after-shrinking, and scalar-action descriptions. I wrote out both surjectivity and injectivity of the germ map using Step 1, including shrinking inside the intersection of the two target neighbourhoods. The displayed formula checks that the bijection is linear over the target local ring with scalars restricted through the canonical local-ring map. Thus there is no hidden comparison-of-module-structures lemma or an equality of unrelated module objects.

For Step 6 I checked the new node's complete statement against 05B8(2–3): it has a finite morphism, a point and its image, the full singleton fibre, and the additional finite-presentation assumption for its second conclusion. These are exactly the item's assumptions. The finite-extension module lemma then applies to the stalk module over the source local ring, and the scalar-compatible isomorphism from Step 5 transports finite presentation. The new lemma is genuinely smaller than the item: 05B8 proves it by choosing affine coordinates, using 00EA to identify S localized at the base prime with S localized at the unique prime above it, and localizing finite module generators and a finite polynomial presentation. No arbitrary module's finite presentation or pushforward equivalence occurs in that argument.

I checked small cases: an identity morphism, a closed immersion defined by a finitely generated ideal, and the finite non-flat thickening Spec(k[e]/(e^2)) to Spec(k) all satisfy the conclusions, including the local-ring lemma. The zero quasi-coherent module causes no exception, and the point assumptions exclude an empty fibre. The proof works without reducedness, flatness, or Noetherian assumptions. The finite-presentation hypothesis must not be dropped: for R=k[x1,x2,...] and S=R/(x1,x2,...), Spec(S) to Spec(R) is finite with singleton fibre at the relevant maximal ideal, but S is finitely presented over itself and not over R, nor over the localized base at that ideal. The singleton hypothesis is used exactly in the shrinking and source-stalk identification; with two disjoint copies of a base, a module with good presentation on one branch and bad presentation on the other illustrates why information at just one chosen fibre point would not suffice.

I reviewed delivery-errors B through E against the actual files. Every non-elementary input in the six steps is named in `uses`, and I read every cited node's statement before copying its exact used clause into `citations.json`; in particular, a definition is used only for its explicit defining argument. No new clause of the item has been packaged as a dependency. The genuine local-ring lemma was not replaced by an essential-finite-type statement. There are no non-elementary steps longer than 2000 characters (all six are below 900), and no omitted “standard comparison” inside a long step. The germ argument is written out and the algebraic singleton-fibre input is separated as the new node.

All twelve new Mathlib queries are the actual outputs logged by `msearch.py`: for each statement I ran LeanSearch, Loogle, two LeanFinder phrasings, and two grep patterns. I read their hits and relevant sources. The finite-presentation hits give definitions and affine criteria already reused; finite-type stalk hits give essential finite type; localization-of-localization gives a general isomorphism only after an appropriate localization has already been supplied. None is the new finite singleton-fibre stalk-ring theorem or the item's full module comparison. The existing four inherited searches on the item were retained. No search was fabricated and no search service was recorded as unavailable when it returned results.
