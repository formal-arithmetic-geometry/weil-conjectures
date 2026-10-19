1. Files written:
   - `dag/nodes/sec-deligne-laumon-a1/lem-per-flat-constant-relative-dimension.json`: statement split, no new nodes, no Mathlib leaf for the target formula.
   - `citations.json`: verbatim citations for every node used by every proof step.
   - `searches.jsonl`: mandatory leanfinder, loogle, grep, and leansearch searches recorded by the search tool.
2. Attachments: none.
3. WANTED: none.
4. What was wrong or incomplete: the imported item had an empty proof. The statement itself agrees with Stacks Morphisms Tag 0AFE (with relative dimension expressed pointwise on all scheme-theoretic fibres), so I left it unchanged. The proof now makes the open shrinking and surjectivity argument explicit and uses existing DAG nodes for openness, local-ring dimension, fibre stalks, and the supremum formulas. No dependency was cited without being used.
5. What could not be finished: nothing.

## Review by Q139

I read the item source in `literature/stacks-project/morphisms.tex`, Tag 0AFE (`lemma-rel-dimension-dimension`), including the part that shrinks source and target, uses openness to arrange surjectivity, applies the flat local dimension formula of Tag 00ON, and takes suprema as in Properties Tag 04MU. I also read every existing node cited by the five proof steps: `def-kun-topological-dimension-at-point`, `pqf-lem-lft-fp-locnoeth`, `lem-weil-pbc-flat-lfp-open`, `pqf-def-locnoeth`, `def-weil-flat-morphism`, `def-weil-finite-type-morphism`, `def-pc-scheme-fibre`, `lem-weil-pbc-dimension-at-point-open-subspace`, `lem-weil-pbc-dimension-supremum-local-dimensions`, `lem-weil-pbc-flat-height-formula`, `lem-sbc-scheme-fibre-stalk-quotient`, and `lem-pc-scheme-dimension-local-rings`. The exact statements used from each are copied into `citations.json`.

Step 1 checks the hypotheses needed for the openness leaf: the target is locally Noetherian and the morphism is locally of finite type, so it is locally of finite presentation. I verified the two-stage shrinking: first intersect a source neighbourhood realizing `dim_x X` with the inverse image of a target neighbourhood realizing `dim_y Y`; then take its open image. The local-dimension minimum shows both resulting global dimensions remain the original local dimensions, and the restricted map is surjective by construction.

Step 2 checks that open restrictions remain locally Noetherian, flat, and locally of finite type, using the cited definitions and the open-subscheme clause. The fibre definition identifies each restricted fibre with an open subspace of the original fibre, so the cited open-subspace dimension lemma preserves the assumed value `d` at every fibre point. I checked that no global finite-type or separatedness hypothesis is introduced.

Step 3 uses the cited topological supremum lemma exactly as stated: because the restricted map is surjective, every fibre is nonempty, and because all its pointwise local dimensions are `d`, its global topological dimension is `d`. The empty-fibre case is therefore irrelevant after the replacement.

Step 4 was checked against the cited statements point by point. The stalk map is flat by the flatness definition; local rings are Noetherian because the restricted schemes are locally Noetherian. The flat height formula gives the base local-ring dimension plus the quotient local-ring dimension, and the cited fibre-stalk quotient identifies that quotient with the local ring of the scheme-theoretic fibre. The local-ring supremum lemma applies to the source, target, and every fibre. Grouping the source supremum by fibres and using the already established fibre dimension `d` gives `dim X = dim Y + d`; the only remaining manipulation is the elementary supremum rearrangement, including the extended value `+∞`.

Step 5 transfers the equality from the chosen open schemes back to `X` and `Y` with the cited equality of local dimensions on open subspaces. I checked the edge cases `d=0`, the identity map, vacuous empty-source assertions, and infinite base dimension. The mandatory Mathlib searches found the existing openness declaration `AlgebraicGeometry.UniversallyOpen.of_flat` and no exact target formula; those results and the two no-hit phrasings are recorded in the item.
