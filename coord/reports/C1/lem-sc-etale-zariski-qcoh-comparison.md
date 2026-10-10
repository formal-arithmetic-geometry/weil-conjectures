# Worker report: lem-sc-etale-zariski-qcoh-comparison

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-etale-zariski-qcoh-comparison.json`: item split into five proof steps; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-etale-cohomology-over-open.json`: statement-only unsplit helper for the localized-site/cohomology-over-an-open identification; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-zariski-module-abelian-cohomology-agree.json`: statement-only unsplit helper; no Mathlib match.

## Attachments

None. I searched the source checkout by the item id, its key phrases, and the blueprint tag; no sorry-free declaration states this comparison.

## WANTED

None. The cited Stacks sources are the checked-in `descent.tex`, `etale-cohomology.tex`, and `sites-cohomology.tex` documents named in the nodes.

## What was wrong in the node, blueprint, or brief

The returned split was repaired by deleting the circular higher-direct-image helper. Step 3 now proves local vanishing directly from the affine etale vanishing theorem, the localized-site comparison, and sheafification; Zariski affine vanishing is no longer cited. Step 2 now states the restriction isomorphism `epsilon_* F_et ~= F_ab`, including compatibility with open restrictions and naturality, using the open-immersion module pullback node. Step 5 now gives the four naturality squares, cites the module/abelian comparison, and derives degree zero from the triangle identity and its degree-zero clause. The unrelated module-cohomology fmap citations were removed from the proof and tool uses.

## What could not be finished

The two helper nodes are intentionally statement-only and remain in the Stage 1 queue for later splitting.

## Review by C1

I read Stacks Descent Proposition 03DW(2), Etale Cohomology Theorem 03P2 and Lemma 03P1, Cohomology on Sites Lemmas 03F3 and 03FD, and the cited DAG nodes. The item's statement still matches 03DW(2). The only new node is the statement-only localization/cohomology-over-an-open fact from 03F3 and 03S2; its hypotheses and naturality clauses are explicit and its Mathlib searches found no match.

Step 1 uses the definition, presheaf functoriality, descent, and abelian-sheaf statements, which say exactly that the assignments and restrictions form the required sheaf and morphism. Step 2 uses the site morphism, pullback, site-cohomology definitions, the new open-object comparison, the natural open-immersion pullback isomorphism, the associated-etale definition, and the module/abelian comparison; these give the map, the restriction-compatible identification `epsilon_* F_et ~= F_ab`, and its source. Step 3 uses only the new open-object comparison, affine etale acyclicity, the sheafification description of higher direct images, and the sheafification definition; it concludes the sheafification vanishes because sections are locally zero on affine covers. Step 4 uses the exact Leray edge-map clause and the higher-direct-image description, whose hypotheses are supplied by Step 3. Step 5 cites the naturality and degree-zero clauses of the module/abelian comparison and the naturality clause of site pullback; the four displayed squares are respectively module/abelian comparison, the restriction identification from Step 2, site pullback, and the adjunction counit. Every step is non-elementary and every cited quote is recorded verbatim in `citations.json`.

I checked the hypotheses at each use: Step 2 uses an actual open immersion and the natural pullback/restriction unit; Step 3 uses affine opens and quasi-coherent restrictions, then affine coverings to make the sheafification zero; Step 4 applies Leray only after the higher direct images vanish; Step 5 uses an O_X-linear morphism and the stated naturality clauses. Small cases checked were q=0, q>0 on an affine scheme, the identity module morphism, and the empty open (all section groups zero). I searched the whole DAG and blueprint for the 03F3/localized-site statement before creating the new helper and found no duplicate. The returned points were all corrected: no circular helper remains, the open-immersion restriction identification is cited and stated, the four naturality squares and degree-zero triangle are explicit, and the obsolete fmap nodes are gone from proof_deps and tool_uses.

The proof uses generic site and affine comparison lemmas from other units as tools; each is declared in `split_report.tool_uses` with the reason it is needed because the `sk-prop-cd` route has no replacement node for that infrastructure.
