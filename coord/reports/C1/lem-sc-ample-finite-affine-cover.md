## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-ample-finite-affine-cover.json`: item split into two proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node and step.

## Attachments

None. No Lean declaration states the item.

## WANTED

None.

## What was checked

The item statement was read against `dag/nodes/sec-curve-estimates/lem-sc-ample-finite-affine-cover.json` and Stacks `properties.tex`, Definition 01PS. The existing `def-weil-pbc-ample-invertible-module` node was read in full; it states the pointwise affine principal-open condition, that each nonvanishing locus is open, and that ampleness includes quasi-compactness. The existing `def-weil-pbc-quasi-compact-scheme` node was read in full; it states exactly the finite-subcover property used in the second step.

Step 1 applies the pointwise affine principal-open clause of the cited ampleness definition to each point, and uses the same definition for openness, so the resulting loci really form an open cover. Step 2 uses the cited ampleness clause to obtain quasi-compactness and the cited quasi-compactness definition to select finitely many members; the selected members retain the positive degrees and affine property supplied by step 1. I checked the empty-scheme case (the finite family may be empty), a one-point affine scheme with the trivial line bundle, and the standard two-chart cover of `P^1` by `O(1)`. No statement or dependency needed correction, and no new supporting node was required.

## Mathlib searches

The required searches were run for this item. LeanFinder returned generic affine-cover declarations but no ampleness theorem; a valid Loogle query returned `AlgebraicGeometry.Proj.affineOpenCover` and related Proj cover declarations, not this statement; the Mathlib grep found no exact ample finite principal-open theorem. LeanSearch was unavailable and is recorded as unavailable in the node's search log. The earlier node searches already recorded no exact match as well.

## Review by C1

I checked every cited statement against its source node rather than relying on the citation names. In step 1, the ample-definition node says exactly that each point has a positive tensor power section with affine nonvanishing locus and that every such locus is open; these are precisely the facts used. In step 2, the same node explicitly includes quasi-compactness, while the quasi-compactness definition explicitly says every open cover has a finite subcover; these statements justify the finite extraction without silently assuming a stronger affine-cover lemma. I verified all hypotheses and checked the edge cases above, and confirmed that the proof dependencies are exactly the two cited nodes. The split introduces no unsupported intermediate claim and leaves the item statement unchanged.
