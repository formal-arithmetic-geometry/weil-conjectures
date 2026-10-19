## Files written

- `lem-trf-ample-affine-limit-descent.json`: statement node, split with five proof steps, no new nodes.
- `citations.json`: verbatim citations for every step/node use.

## Attachments

None.

## WANTED

None.

## Source and dependency checks

The item statement and proof were checked against Stacks Project `literature/stacks-project/limits.tex`, Tag 09MT (`lemma-limit-ample`) in the affine transition-limit situation. I also read the imported statements of every cited node. The definition of ampleness supplies local affine nonvanishing opens; quasi-compactness gives a finite subcover. The fixed module $L_0$ is quasi-coherent because it is invertible, so the existing quasi-coherent section descent node applies directly to every chosen section. The affine-transition limit node gives the restricted inverse systems on principal opens, and the affine-stage node gives eventual affineness because the corresponding limit principal opens are affine. Finally, the compact-open descent node's eventual-equality clause turns equality of the finite union with the whole limit into a stage where the union is the whole scheme. The final step is exactly the ampleness definition.

I searched the whole DAG for Tags 09MT, 01Z0, 01Z6, 01YX, `lemma-limit-ample`, and the relevant section/affine-limit keywords; the existing nodes cited above cover all dependencies. The Mathlib searches were run through `msearch.py` and are recorded verbatim in the node. No new node was necessary, and there are no duplicate nodes to report.

## Review by NY

I read the item source at Limits Tag 09MT and verified every hypothesis: the index is nonempty directed, stages are quasi-compact and quasi-separated, transitions are affine, the limit exists with projections, and the initial line bundle is invertible. Step 1 uses only the ampleness definition and quasi-compactness to obtain finitely many affine principal opens. Step 2 uses the definition's quasi-coherence clause and the existing section-continuity statement to descend each chosen section of the fixed pullback of $L_0$; the finite common upper bound is elementary directedness. Step 3 uses the affine-transition-limit statement for the restricted principal-open system and the affine-stage statement for eventual affineness. Step 4 uses the compact-open descent statement's eventual equality clause on the finite union and the whole stage; affine pullback along the affine transitions is immediate from the affine-morphism definition. Step 5 checks the descended module, affine principal opens, finite cover, and quasi-compact stage against the ampleness definition.

I checked small edge cases: a one-point directed index set reduces to the definition; the zero-rank-free case is excluded because the line bundle is invertible; a single section ($m=1$) and an empty scheme are handled by the same finite-cover argument (the item assumes a nonempty index, while the scheme itself may be empty). No statement was changed, no SGA source was used, and no Lean or compiler tools were run.
