1. Files written:
- `dag/nodes/sec-picard-framework/lem-pc-fpqc-descend-closed-immersion.json`: repaired item, now split into the Tag 02L6 affine and stalk-surjectivity route.
- `dag/nodes/sec-picard-framework/lem-pc-local-flat-faithful-flat-reflects-surjective.json`: new statement-only intermediate node; no Mathlib exact match attached.

2. Attachments: none.

3. WANTED: none.

4. What was wrong in the returned delivery: the node `lem-pc-fpqc-descend-immersion` asserted fpqc descent of arbitrary immersions, but the Stacks source only proves immersion descent fppf-locally (and uses Tag 02L6). I deleted that node and removed its citation. The previous report also incorrectly said the Tag 02L6 source was absent; I read `/home/ubuntu/c1-stacks-review/descent.tex`, lines 5967-6000, including the closed-immersion proof, and lines 6306-6344, including the separate fppf-only immersion section. The repaired proof follows lines 5978-5999: affine descent, flat base change of the structure-sheaf pushforward, faithful-flat reflection of stalk surjectivity, and the affine closed-immersion criterion.

5. What could not be finished: the new faithful-flat reflection node is intentionally statement-only for the next stage, as required for a non-Mathlib intermediate fact.

## Review by M1
I checked the item against Descent Tag 02L6 (label `lemma-descending-property-closed-immersion`) in `/home/ubuntu/c1-stacks-review/descent.tex`, lines 5967-6000. I also read the nearby section at lines 6306-6344, where Stacks explicitly says immersion is only fppf local and proves it using 02L6; this confirms that the deleted arbitrary fpqc immersion node was invalid. The item statement matches 02L6 hypothesis by hypothesis: a morphism `f`, an fpqc covering family, the fibre-product base changes, and closedness of every base change.

Step 1 cites the exact affine clause of `lem-weil-pbc-closed-immersion-integral-separated-uc` and the conclusion of `lem-weil-pbc-fpqc-descend-affine`; these statements say respectively that a closed immersion is affine and that affine base changes over an fpqc covering make `f` affine. Step 2 cites `lem-pc-flat-base-change-cohom` for the `i=0` structure-sheaf base-change isomorphism, `lem-weil-pbc-closed-immersion-affine-cover-criterion` for surjectivity after each closed immersion base change, and the new node for faithful-flat reflection of a surjective tensor map. I checked the hypotheses used here: an affine morphism is quasi-compact and quasi-separated, each covering map is flat, and choosing `y_i` over `y` is exactly the covering condition. Step 3 cites `lem-weil-pbc-locally-surjective-iff-stalks` to pass from all stalk maps to sheaf surjectivity, `pqf-def-affine-morphism` for affine preimages of affine opens, and the affine-cover criterion for the closed immersion conclusion. Every citation quote in `citations.json` is copied verbatim from the cited statement.

For the new node I searched the DAG and blueprint first; no node stated the combined local-flat/faithful-flat reflection fact. Its source is Algebra Tags 00HR and 00HB. I recorded LeanSearch, Loogle, and Mathlib-source grep results; Mathlib has the component declarations (`Module.FaithfullyFlat.of_flat_of_isLocalHom` and faithful-flat exactness reflection) but not this exact combined scheme-stalk statement, so the node remains unsplit. I tested the statement on the identity local map and on a field extension, where tensor-surjectivity and ordinary surjectivity agree. The invalid immersion node and the stale `WANTED` claim were removed.
