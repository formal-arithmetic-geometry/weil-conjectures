# Worker report

Item: `lem-weil-pbc-proper-locally-acyclic-specialization`. Group N0. Date: 2026-10-17.

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-proper-locally-acyclic-specialization.json`: retained the imported statement and five-step Tag 0GJW split, marked `status: split`, and updated the split audit summary; no new nodes were needed.
- `citations.json`: 26 literal statement excerpts, one for every cited dependency at every proof step.
- `report.md`: this report. `searches.jsonl` contains the four searches run for this item.

## Attachments

None. I searched the read-only `WeilConjectures/` source for the item id, the imported declaration name, and the proper locally-acyclic specialization terminology. No sorry-free project declaration states this item. The similarly named stage-2 record in the DAG is only a statement record and is not an attachment.

## WANTED

None. The Stacks Project source and all cited DAG statements are present locally.

## Corrections and route

The imported statement agrees with Stacks Tag 0GJW (lemma `sp-isom-proper-torsion-loc-ac`) specialized to `K = G[0]`: properness and torsion are hypotheses of the item, while local acyclicity is the hypothesis used for the closed-fibre unit. I retained all five proof steps. I did not create a node for the long fourth step: after checking it line by line, it is one routine K-injective representative calculation identifying the fibre exchange map with restriction, and it uses the existing termwise-exchange and cohomology-pullback definitions. No statement dispute, duplicate, or missing dependency was found.

## Review by N0

I read `literature/stacks-project/etale-cohomology.tex`, Tag 0GJW and the referenced Tag 0DDF/0GJV arguments, together with the current `sec-proper-base-change` chapter and `sk-thm-properbasechange` unit. I read the complete statement of every node in `proof_deps`; the 26 citation entries are literal substrings of those statements. The item’s definitions of proper morphism, torsion abelian etale sheaf, local acyclicity, strict henselization, derived direct image, geometric stalk, and pointed-neighbourhood specialization match the cited definitions and the Tag 0GJW specialization.

Step 1 uses `lem-weil-pbc-local-acyclicity-closed-fibre-unit` for the strict-henselized diagram and invertible closed-fibre unit, `lem-weil-pbc-strict-henselization-functoriality` for the closed lift and local ring, `lem-weil-pbc-proper-fp-permanence` for proper base change, and the scheme-convention, closed-immersion, affine-morphism, and affine-permanence statements for the qcqs checks. I checked that the geometric point is affine, that its base change remains affine, and that proper finite-type morphisms have the required quasi-compact and quasi-separated properties.

Step 2 applies `thm-weil-pbc-bounded-below` to the proper geometric-point squares and uses `lem-weil-pbc-cohomology-pullback-derived-unit`, `lem-weil-pbc-geometric-point-pullback-stalk`, and `def-weil-pbc-derived-inverse-image` exactly for the fibre comparison and the exact stalk/global-sections identification. The complex is `G[0]`, so its cohomology is torsion and the theorem’s bounded-below hypothesis is met.

Step 3 invokes the closed-fibre unit, the direct-image definition, and `lem-weil-pbc-inverse-image-stalk-germ` to show that the pulled-back sheaf remains torsion. The cited `lem-sbc-qcqs-higher-images-prime-torsion` is applied to the qcqs map `h` from step 1 with the set of all primes; this gives elementwise annihilators and does not assume a uniform exponent or finite stalks. I checked that the cohomology sheaves of `Rh_*G_{\bar t}[0]` are precisely these higher direct images.

Step 4 applies the fibre comparison to `f'` and the bounded-below torsion complex `K'`. `lem-weil-pbc-strictly-henselian-etale-acyclic` and `lem-weil-pbc-strictly-henselian-sections-stalk` justify replacing the closed stalk by global sections on the strict local base. `lem-weil-pbc-cohomology-pullback-derived-unit` gives the Leray identification, while `lem-weil-pbc-derived-exchange-termwise`, `def-weil-pbc-underived-exchange`, and `def-weil-pbc-cohomology-pullback` state the representative-level maps used to check that the exchange fibre map is literally restriction followed by the inverse of the closed-fibre unit. The 2138-character step contains no hidden independent lemma: it spells out this one map comparison, including the K-injective resolutions and all comparison maps.

Step 5 uses `lem-weil-pbc-specialization-cospecialization-compatibility` for the equality `cosp · rho_t · sp = rho_s`; steps 2 and 4 supply invertibility of the other maps. The exact inverse-image and geometric-point global-sections statements justify passage from derived cohomology to each `R^q f_*G` stalk and identify the resulting map with the item’s pointed-neighbourhood specialization. I checked `q = 0`, higher `q`, and the zero/torsion edge cases; no finiteness or smoothness assumption is introduced.

For each cited node I checked that the quoted text states the fact used, rather than merely naming a definition. The proof dependency list is exactly the union of the five `uses` lists. Required Mathlib searches were rerun with two natural-language/name phrasings: LeanFinder and LeanSearch returned only generic stalk-specialization identities, Loogle returned no usable match, and the Mathlib grep returned none; therefore the item is not a Mathlib leaf. No new node or duplicate check is applicable beyond the cited existing dependencies.

## Unfinished work

None for this one-level stage-1 split. No Lean file was written and no compiler, Lake, or build tool was run.
