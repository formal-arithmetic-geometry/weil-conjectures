1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-derived-open-shriek-derived-adjunction.json` (statement, split; 0 new nodes)
   - `citations.json` (four verbatim step citations)
   - `report.md`

2. Attachments: none. The sorry-free declarations `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction` and `ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction` concern scheme-specific étale/pro-étale coefficient categories, so neither states the arbitrary ringed-space item exactly.

3. WANTED: none.

4. The imported item had no proof. I checked the statement against Cohomology Tag 08BT (`cohomology-lemma-adjoint-lower-shriek-restrict`) and its exact-functor/derived-adjunction proof. Step 1 reads the exact extension-by-zero/restriction statement in `lem-sc-derived-open-restriction-adjunction-exact` and the exact-functor derived factorization statement in `lem-weil-pbc-exact-functor-derived-factorization`; those statements supply the exactness, underived adjunction, and termwise derived functors under the stated module-category hypotheses. Step 2 reads the generic derived adjunction statement in `lem-pc-derived-adjoint-functors`, including its everywhere-defined hypothesis and bifunctorial Hom bijection, and uses `def-weil-abstract-derived-category` for the localization-derived categories. I searched the DAG for the Stacks tags and the extension-by-zero/derived-adjunction keywords before editing; the exact-functor and generic derived-adjoint nodes already state the needed prerequisites, so no child node was created. Small cases (zero complexes and complexes concentrated in one degree) reduce to the underived adjunction termwise, as required.

5. What could not be finished: no source declaration exactly matching the arbitrary ringed-space statement was found; the item remains a natural-language split pending the second worker's review.

## Review by H1

I read the item's source reference (08BT) and the full statements of every cited node. Step 1 uses only the exactness and underived adjunction explicitly stated by `lem-sc-derived-open-restriction-adjunction-exact`, then takes from `lem-weil-pbc-exact-functor-derived-factorization` exactly its clause that every termwise complex represents the induced derived functor. Step 2 uses the everywhere-defined derived-adjunction hypothesis and natural Hom bijection stated by `lem-pc-derived-adjoint-functors`; the localization meaning of the derived categories is the clause quoted from `def-weil-abstract-derived-category`. I verified that the open restriction appearing in the conclusion is the termwise functor supplied in Step 1, and that no additional hypotheses are used. The only correction to the imported node was replacing its empty proof with these two source-aligned steps and recording the two generic cross-unit lemmas as tool uses.

## Second reading by H1

- Item statement: checked against Cohomology Tag 08BT, `cohomology-lemma-adjoint-lower-shriek-restrict`; verdict: hypotheses and derived adjunction agree, including arbitrary ringed spaces and open inclusions.
- Step 1: checked against the statements of `lem-sc-derived-open-restriction-adjunction-exact` and `lem-weil-pbc-exact-functor-derived-factorization`; verdict: exactness, adjunction, and termwise derived functor computation are all stated there.
- Step 2: checked against `lem-pc-derived-adjoint-functors` and `def-weil-abstract-derived-category`; verdict: the everywhere-defined hypotheses and natural Hom bijection apply to the two module categories and their localized derived categories.
- New nodes: none; existing DAG nodes were searched by identifier, Stacks tags, and derived-adjunction keywords, and no duplicate or Mathlib leaf was created.
- Small cases: zero complexes and complexes concentrated in one degree reduce to the underived adjunction; field and empty-open cases introduce no additional hypothesis.
- Changed: corrected the source tag and label from 08BW (Mayer–Vietoris Hom) to 08BT (`cohomology-lemma-adjoint-lower-shriek-restrict`) in `source`, `proof_origin`, and this report; the proof steps and citations were otherwise unchanged.
