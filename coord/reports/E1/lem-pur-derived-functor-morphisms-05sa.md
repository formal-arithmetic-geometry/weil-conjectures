1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-derived-functor-morphisms-05sa.json`: statement node split into four proof steps; no new nodes; Mathlib searches found no exact match.
- `citations.json`: verbatim quotes for every cited node in every proof step.

2. Attachments: none.

3. WANTED: none. The Stacks source was read at `/home/ubuntu/c1-stacks-review/derived.tex` and `/home/ubuntu/c1-stacks-review/categories.tex`, which contain Lemma 05SA(2), Situation 05S8, Definition 05S9, Remark 05Q4, and the localization Hom-colimit statement.

4. No statement error was found. The imported item had no proof; its existing Mathlib search records were rerun, with the unavailable services recorded as unavailable. No new node was created because the argument uses the reviewed pointwise Kan-extension bridge and the existing localization Hom-colimit lemma.

5. Nothing remains unfinished.

## Review by E1

I checked the item against Stacks Lemma 05SA(2), including its left-derived diagram and the uniqueness clause. Step 1 uses the reviewed pointwise Kan-extension bridge, whose statement supplies the limit cone at each derived value and identifies its denominator projections. Step 2 uses that limit statement and the localization functor from Situation 05S8 to construct the map by precomposition with Q(f); this is the ordinary universal property of a limit. Step 3 checks the exact denominator square from the bridge's projection formula and the equality f∘s = s'∘f'. Step 4 uses the existing localization Hom-colimit bijection to show denominator objects jointly determine all structured-arrow projections, so the map is unique. I read both cited node statements verbatim, verified every quote in `citations.json`, checked that all hypotheses (triangulated categories, exact F, saturated compatible S, localization Q, and essential constancy at X and Y) are present, and tested the construction on identity denominators and on f itself. The blueprint ancestor and its 05SA(2) place are recorded in the item; no duplicate or additional node was needed.

## Second reading by E1

- Item statement: checked against Stacks Situation 05S8, Definition 05S9, and Lemma 05SA(2); hypotheses and the functoriality/uniqueness conclusion agree, including identity-denominator and zero-morphism edge cases.
- Step 1: checked against the reviewed pointwise Kan-extension bridge statement; its limit vertex and denominator projections are exactly the data used. Verdict: sound.
- Step 2: checked against the bridge and localization definition; corrected the precomposition order from `Q(f)∘φ` to `φ∘Q(f)`, which is the typed composite. Verdict: repaired.
- Step 3: checked against the bridge projection formula and the 05SA denominator square `f∘s = s'∘f'`; the induced equation and postcomposition by `F(s')` are valid. Verdict: sound.
- Step 4: checked against the localization Hom-colimit bijection and the bridge's RMS2 axiom; expanded the missing denominator refinement argument so every structured-arrow projection is explicitly covered. Verdict: repaired.
- New nodes: none; searched existing DAG nodes and Mathlib records, with no duplicate or exact Mathlib theorem needed.
- Changes: fixed the composition direction in Step 2, supplied the RMS2 refinement and projection factorization in Step 4, and added the corresponding verbatim citation.
