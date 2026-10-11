# Stage 1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-cech-cup-pullback-compat.json`: statement, split proof, metadata; no new nodes.
- `citations.json`: verbatim citations for every non-elementary node use.

2. Attachments: none.

3. WANTED: none. The cited source is present in `literature/stacks-project/cohomology.tex`.

4. Problems found: the imported node was unsplit and its blueprint ancestor is the theorem-of-the-cube node, while the mathematical source is the Cech functoriality and signs in Tags 01FD and 07MB. I preserved the item's statement and recorded the actual Cech route in the split report. No new node was created because a pullback-compatibility or cup-compatibility child would restate clause (a) or (b) of the item.

## Review by J1

I read the item source in `literature/stacks-project/cohomology.tex`, Tags 01FD and 07MB, and checked the existing comparison nodes `lem-sc-cech-comparison-map-naturality` and `lem-sc-cech-comparison-natural`. Step 1 uses the first node for the canonical comparison transformation and writes the refinement cochain map and its differential check explicitly; the morphism-of-schemes refinement is the Tag 01FD diagram. Step 2 is the elementary signed differential calculation, with the tensor-product notion cited. Step 3 uses both existing comparison statements, whose text gives coefficient naturality and identifies the Cech map with sheaf cohomology maps. Step 4 writes the termwise pullback-of-tensor identity and invokes those same comparison statements. I checked the hypotheses: f is a scheme morphism, U and U' are covers with a specified refinement, F and G are quasi-coherent, and all comparison maps are used only when available. Small cases checked were a one-open cover (only degree zero, where the formulas reduce to ordinary pullback and tensor) and degrees p=0 or q=0 (the sign is 1 and the Leibniz identity reduces to the ordinary restriction identity). The Mathlib searches were run for Cech cup products, refinement naturality, and Cech functors; no matching theorem was found, and LeanSearch was unavailable.
The two comparison nodes are declared as generic tool uses because they belong to the Cech-comparison unit, while this item is attached to the theorem-of-the-cube route; the route metadata records why those tools are necessary.

5. Unfinished: none.

## Second reading by J1

- Item statement: checked against Stacks Tags 01FD, 07MB, and 0FKV; corrected clause (a) to canonical-map compatibility and clause (b) to the 0FKV compatibility diagram.
- Step 1: checked against Tag 01FD and the cited Cech, pullback, injective-resolution, and total-complex statements; refinement and the comparison square are now written explicitly.
- Step 2: checked against Tag 07MB; replaced the false degree-p,q sign formula for degree-zero sheaves by the total-complex sign calculation and its degree-zero specialization.
- Step 3: checked against Tag 0FKV and both comparison statements; the conclusion now asserts compatibility without requiring comparison isomorphisms.
- Step 4: checked termwise using pullback and tensor definitions; refinement composition and coefficient naturality are stated explicitly.
- New nodes: none; existing-node search found the comparison tools and tensor-complex definition, so no child node was justified.
- Changed the item statement, proof dependencies, and four proof steps to match the source and restore the repository's recorded 0FKV correction.
- Added the missing tensor-complex dependency and citation entries for the newly cited foundations.
