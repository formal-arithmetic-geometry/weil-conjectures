# Stage-1 report: lem-sfb-ferrand-etale-scheme-patching

Group NY; 2026-10-24. Direct delivery, worker self-review.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ferrand-etale-scheme-patching.json`: statement split, ten complete steps, 30 existing dependencies. Mathlib verdict: no match after the logged semantic, Loogle and source searches and a second phrasing.
- `citations.json`: 40 step/node entries quoting the cited statement verbatim, including every clause taken from multipurpose nodes.
- `report.md`: this report.

There are zero new nodes and zero Mathlib leaves. Sandbox helper scripts and the search log are working records, not DAG deliveries. The repository and launcher were read only. No Lean file was written and no compiler, Lake or build tool was run.

## Attachments

None. Searches for the exact blueprint tag and Ferrand/pinching/patching in `lean/WeilConjectures/` found no declaration proving this item. The existing `AlgebraicGeometry.Scheme.IsQuasiAffine.of_locallyQuasiFinite` is already attached to `lemma-nagata-zmt-quasi-affine-source`; I read its source at `WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean:72` and used that existing node, not a new attachment.

## Literature wanted

None.

## Problems found and changes

The item's statement is correct and unchanged. Its source's separated etale equivalence (0ECL) by itself does not include a counit for a nonseparated etale morphism. The split supplies that argument explicitly: the final flat-algebra assertion of 08KQ gives the counit on affine source/target charts; the affine closed-pinching universal property and Zariski morphism gluing give the global pushout. It actually proves this converse for flat scheme maps. There is no separatedness or quasi-compactness added to the item.

The inherited `blueprint.from.node` is null; `blueprint_refs.py ancestor` confirms that the ancestry has no imported blueprint node. I retained it and its existing via chain and precise place, and searched the full blueprint index for pushout, Ferrand, pinching and affine neighbourhoods. The current latest blueprint direct-image proof (3) was read; it provides no separate Ferrand/etale-patching node. No chapter or unit fields or records were changed; this item is not the unit's key statement.

The initial upstream searches already present in the item were preserved. All searches I added were run through the mandated msearch command and read. The first and second LeanFinder queries return etale category/pullback/base-change and open-gluing declarations, not closed-integral pushout patching. LeanSearch returns separatedness permanence and etale-category declarations, also not the result. The source grep finds no Ferrand/pinching/etale-pushout result. Loogle's index reports unknown identifier `AlgebraicGeometry.IsEtale`, rather than providing a usable candidate; that actual diagnostic is preserved. The source uses `Etale` while some search services return `IsEtale`, so names from service output were not treated as declarations in the local version. I inspected the local etale and gluing files as well as the existing ZMT declaration.

## Not duplicates

No new nodes. In particular I reused `lem-sfb-ferrand-scheme-pushout` (0E25/0E26), `lem-sfb-algebraic-field-image-principal-neighbourhood` (the affine case of 0E21), `lem-sfb-fibre-product-algebra-etale` (08KQ(5)), `lem-sfb-fibre-product-algebra-flat-presentation` (08KQ flat counit), and `lem-sfb-patched-module-base-change` (07RU). The thickening-only scheme-pushout and infinitesimal-etale-patching nodes are insufficient for a general integral pinching and were not cited. The general finite-pinching descent node has a finite hypothesis and was not used for the arbitrary integral map.

## Review by NY

I read Stacks `more-morphisms.tex`, Situation 0ECI, preparation 0ECJ, construction 0E25, separatedness 0E26, functor 0ECK and equivalence 0ECL in full. I also read the affine patching statement and argument of `more-algebra.tex` 08KQ and the module base-change statement 07RU, and `limits.tex` 0E21, including its proof. There are no new-node sources to review. I read the chapter/unit records and the newest blueprint direct-image proof (3), and followed its inherited schematicity subroute rather than replacing the unit theorem.

For step 1 I checked the fibre-product universal property, closed-immersion and integral base-change statements. The specified phi makes both component squares cartesian, so each is applied to its actual base change. The definition of integral gives an affine fibre algebra integral over the residue field, not an integral domain. Affine qcqs supplies its quasi-compactness. For step 2 the affine-open basis and quasi-compactness provide a finite union of affines containing that image. The cited qcqs permanence statement applies since the target A is affine and hence quasi-separated. The etale ring-map quasi-finiteness statement gives finite generation and quasi-finiteness on the affine charts, precisely the local hypotheses of the existing ZMT source theorem. Separatedness of the open restriction follows by restricting the already closed diagonal, as written. I corrected the draft to cite affine qcqs explicitly instead of leaving it implicit.

For step 3 the cited principal-neighbourhood node really permits an arbitrary ring homomorphism to any algebra integral over a field; it requires neither injectivity nor a finite-dimensional or reduced algebra. Embedding Q into an affine scheme reduces exactly to that statement's affine ambient-space formulation. This is why no duplicate general ample-neighbourhood lemma is needed. I explicitly cited the principal-localization open-immersion statement to identify its D(f) as an affine scheme. Step 4 then applies the existing Ferrand construction with all three hypotheses now verified, and the colimit node supplies uniqueness and the induced morphism. No existence argument is hidden in a new clause node.

For step 5 I checked that the Ferrand node states a compatible affine cover, a fibre-product ring, surjectivity of the closed-immersion ring map, and the pushout property after every open restriction. This is stronger than just abstract existence and is what permits the two-stage choice of W and V. The affine fibre-product formula and the affine closed-immersion definition supply exactly C1 = A1/IA1 = B1 tensor_B C, with phi as the common identification. Step 6 uses the etale algebra patching node with its precise ring substitution, without a nilpotence hypothesis; the affine etale criterion and source/target-locality node give the scheme result. The source-open restrictions are etale by the cited open-immersion and locality statements. Step 7 uses the explicit canonical maps in the module base-change node, not an abstract equivalence: the maps are ring maps and bijective on underlying modules, hence ring isomorphisms. The affine fibre-product node identifies their spectra with the required canonical comparisons, and uniqueness of inverse maps gives agreement on overlaps. The third comparison is a formal iterated fibre product. This verifies the projection and phi compatibility, not just existence of some isomorphisms.

For step 8 I checked that the Ferrand node's separatedness clause only applies when its two input schemes are separated over a common base. I therefore first restrict to a compatible affine W and use the canonical comparisons of step 7, separated base change and the existing separated-over-affine theorem. This makes both restricted sources absolutely separated, so 0E26 applies over Spec Z. The relative diagonal is then a pullback of the absolute closed diagonal, and the separatedness target-open-locality node applies. This avoids incorrectly assuming X or T is separated over the original S, or using a theorem about universally closed covers without citing its hypotheses.

For step 9 I checked that the flat-presentation node explicitly includes its final flat-algebra counit, not merely flatness of a patched algebra. Its hypotheses are an arbitrary surjection and a flat algebra, and etale implies flat by the cited definition and affine criterion. The surjectivity after tensor is written as the elementary quotient identity, so it does not assume tensor preserves an injection. The affine pinching node gives the pushout in all schemes, not just affine targets. For step 10 I checked that the morphism-gluing node handles arbitrary open covers and arbitrary scheme targets. Affine refinements exist even when intersections of the chosen affines are not affine; the proof explicitly refines intersections instead of making that invalid assumption. Both uniqueness and existence are checked on these refinements, with no separation or quasi-compactness on U.

I checked B through E of the delivery-errors checklist against the actual node statements: no new-node relabelling, no missing generality in the cited statements, no reliance on a cited proof instead of its statement, and no derived or algebraic-space comparison smuggled into the scheme statement. Every cited node is an existing generic tool; off-unit tools are declared in split_report.tool_uses for maintainer review. All ten steps are shorter than 900 characters, so no step reaches the 2000-character long-step threshold. Their local algebra calculations are explicit rather than asserted as compatibility by transport.

Small cases checked: Z empty gives a disjoint union and the algebra calculation uses C = 0; X, T or fibres empty cause no failure and the principal-neighbourhood theorem allows the zero algebra. If i or j is an isomorphism, the canonical comparisons reduce to identities. Infinite disjoint unions of etale schemes are allowed because covers and gluing are not finite; only the neighbourhood of one quasi-compact integral fibre uses a finite choice. Non-Noetherian and nonreduced integral fibres are allowed throughout. In the converse nonseparated etale examples, including doubled-origin charts, are covered by affine refinement and never assumed separated. No statement dispute or unproved extra hypothesis was found.

## Unfinished work

None at this splitting level. The proof dependencies remain existing DAG work, as required by a one-level split. The server review_split check passed before writing this report; the required full delivery dry run follows.
