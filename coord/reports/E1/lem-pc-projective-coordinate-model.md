# Stage 1 report

1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-projective-coordinate-model.json` — statement, split proof, no new nodes, Mathlib searches found only Proj primitives.
   - `dag/units/sk-thm-picard-coherence.json` — recorded this key node as the unit's realized statement.
   - `citations.json` — verbatim statement quotes for both proof steps.

2. Attachments: none. The tagged declaration `AlgebraicGeometry.exists_isStandard_iso_proj` in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/CurveProjection.lean:42` contains `sorry`, so it is not an attachment.

3. WANTED: none. The blueprint proof is self-contained at the intended natural-language level.

4. The imported node had an uncited second paragraph (`uses: []`, `elementary: null`) and no blueprint split metadata. I made both proof paragraphs explicit, cited the existing Proj and standard-graded definitions, filled the blueprint ancestor/place and `same_as`, and recorded the required Mathlib searches. No new node was created because the only possible auxiliary statement would restate a clause of the item (the quotient/Proj identification).

5. I could not provide a sorry-free Lean proof: the source declaration itself is still `sorry`; this stage only produces the natural-language DAG split.

## Review by E1

I read the item source declaration and docstring in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/CurveProjection.lean` and the imported blueprint proof. The declaration's hypotheses match the item: a field, finite coordinate index, an integral scheme over `Spec k`, and a closed immersion over the base. Step 1 uses exactly the point description in `def-pc-proj` to obtain the homogeneous prime and the standard-graded conditions in `def-pc-standard-graded-algebra` to identify the quotient properties. Step 2 uses the standard-open affine description and graded localization maps from `def-pc-proj`, together with the degree-zero localization notation from `def-pc-standard-graded-algebra`; the empty-chart case and overlap compatibility are written in the step itself. I opened both cited node files and copied the relevant sentences verbatim into `citations.json`. I searched the full DAG and blueprint for a smaller quotient/Proj node and found none; the Mathlib searches returned only topology and Proj primitives, so no Mathlib leaf or duplicate was added. I also checked the small edge case of an empty standard chart: localization at a generator lying in the prime ideal gives the zero ring, matching the empty inverse image.

## Second reading by E1

- Item statement: checked against `AlgebraicGeometry.exists_isStandard_iso_proj` in `CurveProjection.lean:38-48`, including all hypotheses and the over-base isomorphism conclusion; agrees.
- Step 1: checked against `def-pc-proj` and `def-pc-standard-graded-algebra`; the homogeneous-prime, quotient-domain, degree-zero, and degree-one generation inputs are cited and the construction is explicit.
- Step 2: checked against those same definition statements and the Lean Proj chart conclusion; localization, the empty chart, overlap maps, and gluing are stated in the step, with both citations present in `uses` and `citations.json`.
- New nodes: none; B1-B7 and duplicate/Mathlib-leaf checks are not applicable. Existing definition nodes and verbatim citation quotes were opened and checked.
- Edge cases: checked an empty standard chart, a one-point projective scheme, and the zero-dimensional coordinate case; no statement change was needed.

Changes: confirmed the repaired step-2 citation metadata and retained the proof in the step; no auxiliary node was added because it would duplicate the item.
