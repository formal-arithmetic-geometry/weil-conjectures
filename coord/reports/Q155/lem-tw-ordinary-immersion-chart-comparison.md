# Stage-1 delivery: lem-tw-ordinary-immersion-chart-comparison

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-tw-ordinary-immersion-chart-comparison.json`: existing statement node, now split into four proof steps; no Mathlib match for the full statement.
- `citations.json`: a verbatim statement excerpt for every citation in every proof step.
- `report.md`: this report. `searches.jsonl` is the search tool's own log.

No new nodes; no new Mathlib leaves. The item's statement and statement dependencies are unchanged. No unit file, Lean file or repository file was written. The sandbox initially contained only dispatcher brief markers, with no previous item, report, searches or delivery result to reuse.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and for immersion/restriction, derived composition and slice pullback. The exact tag is absent. I read `SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean`, especially `leftDerivedUpperStarComp` at line 226: it concerns module objects over a condensed ring and does not supply the entire ordinary ring-sheaf immersion/chart statement. It is not an attachment. No compiler was invoked.

## WANTED

None. The sources needed for this assembly are available locally.

## What needed repair

The imported item was statement-only. It specifies both the isomorphisms and their normalization, so a proof asserting only an abstract base-change isomorphism would be insufficient. The split now supplies the actual composition path, the represented-slice identification, the structural-ring-map identification, and the direction of the inverse slice comparison.

Bhatt--Scholze Remark 6.8.15 assumes schemes noetherian in its discussion. I read that passage (printed page 62) and do not use it to justify the item's unrestricted scheme generality. Instead I use the existing hypothesis-free statements on projection-defined profinite coefficients, ordinary immersion restriction, ordinary pro-etale composition and arbitrary sheaf slices. This is a source limitation, not a statement correction: no new geometric or completeness hypothesis is added.

## Unfinished work

None for this split. Existing cited unsplit nodes remain separate DAG work; this delivery does not split or edit them.

## Not duplicates

No new node was created. Whole-DAG searches for the source tags and for composition, slice and representable pullback found the existing tools used here. Whole-blueprint searches included `derived pullback`, `pullback composition`, `immersion chart`, `ringed slice` and `representable`. No blueprint node found states this entire immersion-plus-representable-chart comparison. In particular the pro-etale derived composition theorem is a tool for arbitrary compatible coefficient identifications, and the arbitrary-sheaf-slice theorem is the general comparison needed by the second isomorphism; neither needs a new specialization node.

## Mathlib search assessment

I ran the authorized `msearch.py` command for the item using LeanFinder (derived pullback, composition and representable restriction), Loogle (`"SheafOfModules.pullbackComp"`), source grep (`pullbackComp|restrictFunctorIsoPullback` in `Algebra/Category/ModuleCat`), and a second semantic phrasing through LeanSearch (derived inverse image, localization and ringed topoi). All four services succeeded and are recorded verbatim in `searches.jsonl` and the appended `mathlib_searches` records. LeanFinder's completed log was recovered after the interrupted tool session disappeared, before any repeat search. I read the source of `SheafOfModules.pullbackComp`, `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167`: it gives ordinary composition. Other hits concern ordinary free pullbacks, scheme module pullbacks, or Zariski open restriction. None states the whole unbounded derived comparison with these ringed pro-etale slice identifications. Earlier item searches are retained unchanged.

## Review by Q155

I read `GOAL.md`, the stage-1 brief, the stage document, the three blueprint levels in `SETUP.md`, the unit and chapter records, and both occurrences of delivery-errors sections B--E. The unit is the stepless linear-algebra remark `sk-r-real-linear`. This item lies under the already-recorded realization chain for duality of weights; the proof follows its required ordinary composition and covering-chart route. The off-unit statements are generic tools, with their precise uses declared in `split_report.tool_uses`.

For the item source I read Stacks `sites-cohomology.tex`, Tag 0D6D (`lemma-derived-pullback-composition`), including the proof: choose a flat-term K-flat representative, pull it back, and compute the iterated pullback by the ordinary composite. I also read `sites-modules.tex`, Tag 04IF (`lemma-localize-morphism-ringed-topoi`), including the formula for the restricted structural map and the commutative ringed square; `sites.tex`, Tags 04D3 (`lemma-pullback-representable-sheaf`) and 03CE (`lemma-localize-given-products`); and `schemes.tex`, Tag 01JY (`lemma-base-change-immersion`). No SGA route is used. No new node has an additional source to audit.

Step 1 cites the finite-set clause of `lem-weil-pbc-standard-quotients-perfect`, not merely a definition of finite coefficients. This verifies the finite-ring and countability hypotheses of `lem-weil-pbc-profinite-coefficient-inverse-image`. I opened that node and checked that its statement supplies exactly the projection-defined map as an isomorphism for every scheme morphism, with no noetherian hypothesis. This discharges the coefficient-isomorphism assumptions of `lem-weil-pbc-proetale-derived-pullback-composition`. I also opened `lem-tw-completed-coefficient-ringed-coherence`: it explicitly identifies composite ring maps and their finite projections under the canonical geometric compositor. Thus the coefficient map used by the composition theorem is the one in this item's statement, rather than some chosen alternative. No flatness assumption has been silently introduced.

Step 2 uses only clause (1) of `lem-weil-pbc-immersion-base-change-lft` to verify that the base-changed map j is an immersion. Its locally-finite-type conclusion is not needed. I opened `lem-sf-immersion-completed-pullback-comparison` and checked that it states ordinary pullback equals exact immersion restriction; its comparison with completed pullback on derived-complete objects is not invoked. This matters because K is arbitrary here. The two composition isomorphisms come from the statement of the pro-etale composition node, which explicitly includes the flat-term K-flat formula. Applying one forward and the other backward through the common composite gives the requested first map. The central identification uses the equality fj = if_S, with the coefficient comparison proved in step 1. This is an ordinary pullback argument, independent of completed coefficient categories.

Step 3 uses the actual base-change functor in `def-weil-proetale-inverse-image`, whose statement already asserts preservation of finite limits and coverings. `lem-weil-pbc-proetale-subcanonical` supplies the additional hypothesis of `lem-pur-site-representable-algebraic-pullback`; the latter gives the canonical isomorphism f_S^{-1}h_U ≅ h_V and its identity normalization. The representable-slice equivalence is stated explicitly by `lem-weil-pbc-localized-sheaves-over-representable`; no construction hidden in that node's proof is used. I checked that `lem-sbc-ringed-topos-sheaf-slice-derived-comparison` describes the inverse image on objects over the sheaf h_U. Finally the slice clause of `lem-tw-completed-coefficient-ringed-coherence` identifies both sites, both completed coefficient rings, their finite projections and the localized structural map with c_v. This prevents confusing agreement of topoi with agreement of ringed morphisms.

Step 4 invokes the actual statement of the arbitrary-sheaf-slice derived theorem: its theta has direction P_slice r_U → r_V P_f, so its inverse is required after restricting step 2. The same statement says restriction is exact, preserves flat-term K-flat models, and theta is represented by the ordinary comparison. This verifies the second isomorphism, its direction and the requested normalization before completion. The theorem explicitly removes flatness and boundedness assumptions, so it applies to the arbitrary K of the item. Naturality is preserved by restricting, inverting natural isomorphisms and composing them; there is no additional compatibility lemma hidden in this final assembly.

I tested the statements and maps with i the identity, i a closed immersion, an empty stratum, U the final object, U empty, and an identity f. The constructions reduce to composition or restriction in these cases; for the empty sites the module categories are zero, so nothing requires nonemptiness. I checked that no step assumes a stratification, quasi-compactness, finite type, a base field, separatedness, noetherianity, derived completeness, or boundedness. The small-site universe convention is already part of the pro-etale-site definition. Each cited statement was opened, and every entry in `citations.json` is an actual substring of it. A transitive dependency walk found no path from any cited tool back to the item. Each step has fewer than 2000 characters and contains only the stated assembly argument, with non-elementary ingredients cited as nodes. No lemma was hidden in a long inline step and no clause was moved into a new node.

The server-side `review_split` check passed with zero new nodes. The unfilled unit realization noted by that check is pre-existing and outside this non-key item's ownership.
