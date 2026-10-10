1. Files written:
   - `dag/nodes/sec-nagata-compactification/pqf-def-affine-morphism.json`: existing definition node, split with no new nodes; Mathlib search found only generalizations.
   - `citations.json`: empty because the definition has no proof steps.
2. Attachments: none. No sorry-free declaration in `WeilConjectures/` carries the blueprint tag or states the bundled item exactly.
3. WANTED: none.
4. What was wrong in the node, blueprint, or brief: the imported node had no stage-1 metadata. I filled the blueprint origin and alternate-match search, recorded the required Mathlib searches, and added the split report. The statement itself agrees with the blueprint definition and Stacks Morphisms Tag 01S8: affine means affine preimages of affine opens; affine-to-affine morphisms and closed immersions are standard consequences. No proof node is appropriate because this is a definition.
5. What I could not finish: nothing.

## Review by E1

I read the item node, chapter `sec-nagata-compactification`, unit `sk-prop-nagata-sketch-zmt`, and the blueprint search results. The source recorded by the item is Stacks Morphisms Tag 01S8; its definition sentence matches the node hypothesis-by-hypothesis, including the ambient affine-scheme notion and both standard consequences. I searched the slopmaster2 project for the blueprint tag and for affine-morphism declarations; no project declaration states this exact bundled definition, so there is no attachment. I searched Mathlib with LeanFinder, Loogle, and grep. LeanFinder returned `AlgebraicGeometry.isAffineHom_iff`, `IsAffineOpen.preimage`, and `isAffineHom_of_isAffine`; grep confirmed `isAffineHom_of_isAffine` at `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean:181-182` and the closed-immersion affine consequence at `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:317-322`. These are general or component results, not an exact replacement for the definition node. Since the item has no proof steps, there are no cited-node quotes and `citations.json` is correctly empty. I checked the small cases conceptually: a morphism between affine schemes satisfies the definition by the affine-target property, and a closed immersion has affine source over every affine target open by the Mathlib closed-immersion theorem. No statement correction was needed.

## Second reading by E1

- Item statement: checked against Stacks Project `morphisms.tex`, Definition `definition-affine` (Tag 01S8), including that `f : X -> S` is a scheme morphism and every affine open of `S` has affine-open inverse image; the bundled affine-to-affine and closed-immersion consequences are consistent with the source section.
- Proof steps: none, because this is a definition node; there are no cited proof facts or citation quotes to audit.
- New nodes: none; B1-B7, duplicate checks, and per-node edge-case tests are vacuous.
- Edge cases: affine-to-affine morphisms and closed immersions were checked; the empty scheme introduces no additional condition.
- Changes: none. The definition, dependencies, blueprint metadata, Mathlib search records, and empty `citations.json` remain correct.
