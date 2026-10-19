# Worker report: lem-trf-proper-comparison-product

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-comparison-product.json`: statement item, split with four proof steps; no new dependency nodes.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None. I searched the slopmaster2 source for the item id, its key terms, and the blueprint tag; no sorry-free project declaration states this item exactly.

## WANTED

None. The cited Varshavsky PDF is present in `literature/`.

## Existing-node and duplicate checks

The split reuses `def-sf-kv-maps`, `thm-sf-kunneth-relative`, `lem-trf-relative-kunneth-counit`, `def-exchange-projection`, `fix-prop-adjunctions`, `lem-pur-derived-pullback-tensor-iso`, `lem-weil-pbc-proper-base-change`, `prop-functor-package`, `lem-trf-proper-direct-image-comparison`, `def-trf-cohomological-comparison`, and `def-trf-coefficient-pushforward`. I searched the DAG and both blueprint snapshots for the product-comparison statement and for the displayed `Pi^p` formula; no existing node states this exact specialization, so no new node was created and no duplicate pair arises.

## What was checked and corrected

The imported node had no proof, no `proof_deps`, and an unspecified blueprint location. I supplied a proof following Varshavsky §4.1.4(a), the evaluation paragraph of the blueprint `lem-trf-trace-map-exchange` proof, and the prescribed `Pi` formula in `def-trf-cohomological-comparison`. I retained the imported statement and all existing Mathlib search records. I added the exact blueprint proof location, the complete proof dependency union, and the required split report.

## Review by Q41

I read the item source in Varshavsky §4.1.4(a), Notation 4.2.3(ii), the master and main-20261015 blueprint paragraphs for the evaluation calculation, the chapter and unit records, and the full statements of every node cited in the proof. Step 1 uses the construction of `Ku_!` in `def-sf-kv-maps`, the relative Künneth isomorphism, proper identification `Rf_! ≅ Rf_*`, ordinary exchange mates, and canonical pullback/tensor comparisons. I checked that `u=p_1×1` and `v=1×p_2` are base changes of the proper maps `p_i`, using `lem-weil-pbc-proper-base-change`, so the hypotheses of the relative Künneth node apply. Step 2 uses the exact counit-transpose assertion of `lem-trf-relative-kunneth-counit`; I checked that conjugating by the two projection-square mates gives the displayed tensor of the two counits, with the pullback and monoidal identifications supplied by `lem-pur-derived-pullback-tensor-iso`. Step 3 uses the ordinary adjunction bijection and the fact that the canonical Künneth construction is assembled from isomorphisms, so the specified map is invertible. Step 4 opens the proper-direct-image comparison and the cohomological-comparison definition and substitutes `f_X=Rp_{X*}`, `f_{X×X}=R(p_X×p_X)_*`, and `p_1=p_2=p_X`; this gives exactly the item’s final assertion. I tested the edge cases of identity proper maps, maps to `Spec k`, empty schemes, and zero complexes; all displayed composites reduce to the canonical identity/zero maps and the transpose argument remains valid. No source statement or hypothesis was changed.

## What remains

Nothing remains for this stage-1 split.
