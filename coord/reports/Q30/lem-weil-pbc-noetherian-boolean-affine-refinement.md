# Stage-1 report: lem-weil-pbc-noetherian-boolean-affine-refinement

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-noetherian-boolean-affine-refinement.json`: item split into six proof steps; no new node.
- `citations.json`: verbatim statement excerpts for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, the blueprint tag, and the Boolean/Noetherian-affine terminology; no exact sorry-free declaration exists.

## WANTED

None.

## Statement and source review

The statement was checked against Stacks, Tag 095K, `lemma-decompose-quasi-finite-morphism`, proof, final Noetherian partition paragraph. The item is the finite Boolean refinement used there: finitely many closed subsets are made constant on each stratum, with an additional affine and reduced refinement. No hypothesis or conclusion was changed. The imported Mathlib searches were read and show no theorem stating this finite Boolean affine refinement; the returned Noetherian-space and affine-cover declarations are only general ingredients. The empty scheme and the case of no closed subschemes are explicitly included.

## Review by Q30

I read the item source, the chapter and unit records, and the full statements of every cited node. Step 1 uses the definition of a locally closed subset, the closed-then-open factorization of an immersion, fibre products, and reduced schemes to form the finite Boolean atoms and their induced reduced locally closed schemes. I checked that the atoms are pairwise disjoint and cover by the unique membership vector of a point. Step 2 uses the existing Noetherian-open-subscheme leaf; its statement supplies exactly that an open subscheme of a Noetherian scheme remains Noetherian, which applies after taking the finite intersection of the closed affine subschemes. Step 3 uses `lem-zl-affine-partition`, whose statement gives a finite partition into locally closed reduced affine subschemes, and `lem-weil-pbc-proper-fp-permanence` clause (e), which states that immersions compose. Thus every final source is affine and reduced and the images remain disjoint and covering. Step 4 is the direct Boolean membership check, including both values of each bit. Step 5 uses the fibre-product definition, the closed-immersion base-change leaf, and the base-change image formula; these say respectively what pullback is, that the projection is a closed immersion, and that its image is the inverse image of the original closed image. I verified that the inverse image is all or empty on each Boolean atom, and that the closed-immersion homeomorphism onto its image converts this to the required statement about the pullback space. Step 6 checks finiteness and the empty cases.

The only off-unit citation is `lem-zl-affine-partition`; I declared it in `split_report.tool_uses` because it is a generic geometric partition theorem and no node in this proper-base-change unit gives the same input. No new node was created, so there are no duplicate or new-node search issues. The server-side `check_dag` precheck passed.

## Problems or corrections

No mathematical source or statement error was found. The imported node retained its prior `created` metadata naming Q64; this was left unchanged as required by the handoff rule, while the new split and report are authored by Q30.

## Unfinished work

Nothing remains for this stage-1 split.
