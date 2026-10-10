1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-sc-proj-standard-open-basis.json`: statement node, split; no new nodes.
   - `citations.json`: two verbatim step citations.

2. Attachments: none.

3. WANTED: none.

4. Nothing was wrong with the item statement. The imported node had no proof split. Its source is Stacks Algebra Lemma 00JP, part (5), together with Constructions Lemma 01MB. The existing cross-unit node `lem-weil-pbc-proj-standard-open-inclusion` already states the positive-degree standard-open basis clause, so I did not duplicate it. The existing definition node `def-nagata-affine-proj` states the affine identification of each standard open, so no new affine-chart node was needed.

5. I finished the split. No proof obligations or new nodes remain.

## Review by J1

I read the item node, the ancestor `lem-sc-pic-proper-ntorsion`, the unit `sk-thm-curveestimate`, and the source context in `literature/stacks-project/constructions.tex` and the Algebra/Constructions statements recorded in the cited nodes. Step 1 uses only the statement of `lem-weil-pbc-proj-standard-open-inclusion`; its clause (0) says verbatim that the standard opens form a basis, with the same hypotheses that the item introduces. This is declared as a cross-unit tool use because it is a generic Proj-topology result rather than a route-specific node. Step 2 uses only `def-nagata-affine-proj`; its statement says verbatim that a positive-degree homogeneous standard open is identified with the spectrum of the degree-zero homogeneous localization, which gives affineness. The item statement's three notation dependencies define the graded ring, Proj, and homogeneous localization used by these steps. I checked the empty ring/empty Proj case and a polynomial Proj such as `Proj(k[x_0,x_1])`: the basis assertion is vacuous in the empty case and gives the usual two affine charts in the polynomial case; the affine identification is exactly the chart description in both cases. Mathlib searches already recorded on the item found only partial chart/cover declarations, so the item remains a split node rather than a Mathlib leaf. The citation manifest quotes exact substrings of both cited node statements.
