1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-sc-topological-filtered-injective-cech-acyclic.json` — item split; no new nodes; Mathlib searches found no exact result.
   - `citations.json` — verbatim statement excerpts for every cited node in every step.

2. Attachments: none.

3. WANTED: none.

4. No statement error was found. The source declaration `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered` is a different, scheme-etale statement and is sorry-bearing, so it is not an attachment. The existing general-site injective Cech node and the existing filtered-colimit exactness leaf make additional child nodes unnecessary. The finite-cover family is cofinal because quasi-compact opens have a quasi-compact basis and finite subcovers, while pairwise intersections of basis opens are quasi-compact by hypothesis.

5. What was checked: I read Stacks `cohomology.tex`, Lemma 01FF and its Cech-vanishing ingredient Lemma 01EW. Step 1 uses the statement of `lem-weil-pbc-sheaves-directed-colimit-sections` exactly on every quasi-compact finite intersection, together with the Cech term definition; the finite product and restriction compatibility are the direct construction. Step 2 uses the statement of `lem-weil-pbc-site-injective-cech-acyclic` for each injective `I_i`, and the statement of `lem-weil-pbc-filtered-colimit-abelian-groups-exact` to preserve exactness degreewise. Step 3 verifies all three hypotheses of `lem-weil-pbc-site-cech-vanishing-criterion`: the basis and finite intersections give condition (1), the finite-refinement argument gives condition (2), and Step 2 gives condition (3); `def-weil-pbc-sites-and-cohomology` supplies the meaning of `H^q(U,-)`.

   I searched the whole DAG for duplicates and found no node stating this filtered-injective topological result; the reused nodes are strictly more general tools or sectionwise facts. I checked small cases: a one-open identity cover has zero positive Cech cohomology, the zero sheaf gives zero complexes, and a finite cover with repeated opens still has the same finite-product and filtered-colimit argument. Mathlib searches were run with LeanFinder, Loogle, grep, and a LeanSearch request (the latter was unavailable); the recorded successful searches found only generic sheaf or injective-complex declarations, not this theorem.

## Review by J1

I checked the item source and every cited statement directly. The item hypotheses match Lemma 01FF's claim: a filtered colimit of injective sheaves, a quasi-compact basis closed under pairwise intersections, and finite basis covers. For Step 1, the cited sections-colimit node explicitly gives a bijection on sections under the finite-cover and quasi-compact-overlap hypotheses, which is exactly what is needed for each Cech factor; the Cech definition supplies the finite product and alternating restriction maps. For Step 2, the general-site injective Cech node explicitly states positive-degree vanishing for every covering, and the filtered-colimit node explicitly states preservation of exact sequences, so the colimit complex is exact in positive degrees. For Step 3, I checked the criterion's stated conditions against the basis hypotheses and wrote the finite refinement argument, then used its stated derived-cohomology conclusion. No new node was created, no duplicate or circular citation was introduced, and the proof uses only the source route.

## Second reading by J1

- Step 1 checked against Stacks Lemma 01FF (claim, lines 3255-3275), the Cech-complex definition, and the sections-colimit statement; repaired the missing cofinal-cover argument and explicit finite-product/filtered-colimit identification.
- Step 2 checked against Stacks Lemma 01FF (lines 3275-3290), the general-site injective Cech node, and filtered-colimit exactness; verdict sound.
- Step 3 checked against Stacks Lemmas 01FF and 01EW and the stated Cech-to-derived criterion; basis refinement, iterated intersections, and all three criterion hypotheses are present.
- No new child nodes exist; there were therefore no child-node statements to audit, deduplicate, or remove.
- Changed Step 1 and its citation excerpt because the cited sections-colimit node's bijection clause requires a cofinal finite-cover system, and finite Cech products require an explicit filtered-colimit argument.
