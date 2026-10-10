1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-internal-hom-stalk-localization.json`: repaired item proof.
- `dag/nodes/sec-picard-framework/lem-sc-coherent-affine-free-resolution.json`: statement-only node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-derived-hom-finite-free-model.json`: statement-only node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-derived-hom-projective-resolution.json`: statement-only node; Mathlib has only a more general projective-resolution/Ext infrastructure, not this exact statement.
- `citations.json`: verbatim quotes for every non-elementary citation in every step.

2. Attachments: none. The source grep found no sorry-free declaration tagged `(blueprint: lem-sc-derived-internal-hom-stalk-localization)` and no declaration stating this item.

3. WANTED: none.

4. What was wrong and what changed: the returned version moved the item's entire argument into `lem-sc-derived-internal-hom-stalk-general`, which duplicated the item and put bounded-below on the wrong complex. I deleted that node and the unnecessary pseudo-coherence node. The repaired item follows the recommended local route. Step 1 uses the new affine finite-free resolution statement, which combines Tag 01XZ with the existing finite-free module resolution node (Tag 00LP) and affine tilde equivalence. Step 2 uses the new bounded-above locally free Hom model, with `G[0]` visibly bounded below. Step 3 writes the finite-free stalk Hom identification explicitly and marks only that finite-coordinate calculation elementary. Step 4 cites the existing exactness-of-stalks statement and the new projective-resolution RHom statement. Step 5 takes cohomology and records naturality. No pseudo-coherence terminology remains.

## Review by H1

I read the item's Stacks source, cohomology.tex Lemma 0GM8 case (2), and the affine and algebra sources used by the replacement nodes. The item hypotheses are checked in Step 1: Noetherianity supplies a Noetherian affine neighbourhood, coherence supplies a finite module presentation there, and the finite-free resolution node supplies the bounded-above free complex. Step 2 checks the required boundedness orientation: the free complex is bounded above and `G[0]` is bounded below. Step 3 is the direct finite-rank stalk calculation, with no hidden derived assertion. Step 4 uses the exact statement of `lem-weil-pbc-module-stalk-exact` for exactness after taking stalks, then the exact statement of the projective-resolution node for local RHom. Step 5 only takes cohomology and uses the naturality of the displayed constructions.

I opened the statements of all cited nodes before writing `citations.json`; each quote is copied verbatim. I searched the whole DAG and blueprint for the three replacement facts and found no duplicate blueprint node. Mathlib searches were run for each replacement node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. Small cases checked were a one-point affine scheme (the comparison is the identity), `F = O_X` (the Hom complex is `G[0]`), and a finite free resolution of a finite module over a Noetherian local ring. These checks exposed no further statement error.

The existing exactness-of-stalks node is declared as a generic tool use: Step 4 needs this ringed-space fact and the Picard-duality unit has no replacement node for it.

5. What I could not finish: nothing.
