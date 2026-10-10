1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-rational-unramified-cotangent-criterion.json` — statement, split proof, and blueprint metadata; no new nodes; Mathlib searches found no scheme-point criterion.
- `citations.json` — verbatim statement fragments for every cited node in every proof step.
- `report.md` — this report.

2. Attachments: none.

3. WANTED: none. The cited Stacks source is represented in the repository's imported citation metadata.

4. The original item had the correct statement but no proof. I checked the consumer `lem-sc-finite-flat-unramified-tangent-criterion` and its reviewed note, then read the existing affine unramified criterion, localization and base-change lemmas, and the Jacobi-Zariski differential sequence. The split follows the source's local proof: affine localization, conversion of unramifiedness to vanishing relative differentials, identification of the cotangent-map cokernel with the relative differential fibre, and Nakayama. No duplicate node states the rational-point criterion or its exact local sequence. The item and all three Mathlib search forms were run; LeanSearch was unavailable and recorded as such.

## Review by C1

I verified that the hypotheses used in the affine reduction are exactly those of the item: `f` is locally of finite type, `x` and `y` are closed, and both residue fields are `k`. Step 1 uses the scheme conventions and the definition of unramified morphism, with localization of differentials to pass to the local rings. Step 2 uses the existing affine criterion, whose statement says that an affine morphism is unramified exactly when the ring map is finite type with zero Kähler differentials; localization supplies the chosen stalk. Step 3 uses the existing exact differential sequence and base-change statement: after quotienting by the maximal ideal and identifying the common residue field, the map from `m_y/m_y^2` to `m_x/m_x^2` has cokernel the fibre of the relative differentials. Step 4 applies finite generation and Nakayama, then combines Steps 2 and 3. I checked the identity map, the map `t |-> t^2` at `0`, and a map from `Spec(k)` as edge cases; they give respectively an isomorphism, the zero non-surjective cotangent map with ramification, and zero-dimensional cotangent spaces. The citation quotes were copied from the cited node statements and recorded in `citations.json`.

5. Nothing remains unfinished.

## Second reading by C1

- Item statement: checked against Varieties Lemma Tag 0B2G, with the field-base specialization and rational residue-field hypotheses stated explicitly; verdict: agrees hypothesis by hypothesis.
- Step 1: checked affine localization and stalk identification against the scheme conventions, unramified-morphism definition, and Kähler localization node; verdict: cited statements supply the reduction, with no uncited non-elementary fact.
- Step 2: checked the finite-type local ring map and vanishing relative differentials against the affine unramified criterion and localization node; verdict: the criterion applies after localization and the finiteness hypothesis comes from locally finite type.
- Step 3: checked the quotient differential sequence, its exactness/surjectivity, and base-change identification against the Jacobi-Zariski, base-change, and localization nodes; verdict: the cokernel is the residue-field fibre of relative differentials and the displayed cotangent map is the left map.
- Step 4: checked finite generation, Nakayama, and the combination with Steps 2--3; verdict: the final equivalence follows, and the step is elementary once the cited criterion is available.
- New nodes: none; therefore B1--B7, duplicate search, and Mathlib-leaf checks have no new-node cases.
- Edge cases: identity maps, $t\mapsto t^2$ at the origin, and $\operatorname{Spec}(k)\to\operatorname{Spec}(k)$ were checked; verdicts are respectively isomorphism/surjective, ramified/non-surjective, and zero cotangent spaces.

Changes made: replaced the source description with the exact Stacks Tag 0B2G and its supporting Tag 02G6 reference, and added this per-step second-reading record. The existing proof steps, citations, and Mathlib search log were otherwise left unchanged.
