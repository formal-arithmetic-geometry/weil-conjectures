1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-kinjective-comparison-principle.json` (item, split; no new nodes and no Mathlib leaf created).
- `citations.json` (verbatim statement excerpts for every cited step).

2. Attachments: none. No sorry-free project declaration states this item exactly.

3. WANTED: none.

4. The imported item had the correct comparison statement but no proof. I checked the existing DAG for the K-injective comparison principle and found the Mathlib-leaf node `lem-weil-pbc-kinjective-hom-derived`, whose statement supplies the localization Hom bijection. I used it rather than creating a duplicate node. The proof then records that the derived localization inverts quasi-isomorphisms and transports precomposition across the two localization bijections. The item statement and hypotheses were left unchanged.

## Review by M1

I read the item's Mathlib source reference `Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean`, especially `CochainComplex.IsKInjective.Qh_map_bijective` and the quasi-isomorphism inversion result, and read the full statements of `lem-weil-pbc-kinjective-hom-derived` and `def-weil-abstract-derived-category`. Step 1 uses exactly the former node's sentence that for every complex `N`, the map from Hom in the homotopy category to Hom in the derived category is bijective; its K-injective target hypothesis matches `I`. Step 2 uses exactly the definition node's sentence that the derived category is the localization at quasi-isomorphisms, so `Q(s)` is invertible. Step 3 uses functoriality of the localization and the two bijections from Step 1 to conjugate precomposition by `s` with precomposition by `Q(s)`; this is elementary categorical transport, and both cited statements are quoted in `citations.json`.

I checked the hypotheses on the small cases `s = id`, `A = B`, and the zero complexes: the map is the identity or the evident bijection. I also checked that no new node duplicates an existing statement or merely restates a clause of the item. The cross-unit citation is declared as a tool use because it is a generic Mathlib-derived-category fact not supplied by this unit's route. The required LeanFinder, Loogle, grep, and LeanSearch searches were run for the item; LeanSearch was unavailable and recorded as unavailable, while LeanFinder returned the relevant Mathlib declarations and the launcher grep/Loogle services returned no indexed hits.

5. What I could not finish: nothing.

## Second reading by M1

- Item statement: checked against `CochainComplex.IsKInjective.Qh_map_bijective` in the pinned Mathlib source; all abelian-category, derived-category, quasi-isomorphism, and K-injective hypotheses are present. Zero, identity, and equal-source-target cases give the expected bijection. Verdict: agrees.
- Step 1: checked against the statement of `lem-weil-pbc-kinjective-hom-derived` and its verbatim citation; it uses exactly the Hom localization bijection for a K-injective target, at `A` and `B`. Verdict: agrees.
- Step 2: checked against `def-weil-abstract-derived-category` and Mathlib's `isIso_Q_map_iff_quasiIso`; localization makes `Q(s)` invertible, so precomposition has the stated inverse. Verdict: agrees.
- Step 3: checked against both cited statements and `citations.json`; functoriality gives `Q(g \circ s)=Q(g)\circ Q(s)`, and conjugation by the two bijections proves the asserted map bijective. Verdict: elementary categorical transport is sufficient.
- New nodes: none; the existing Mathlib leaf `lem-weil-pbc-kinjective-hom-derived` was checked for duplication and supplies the only auxiliary theorem.
- Repair: corrected sandbox metadata so `created.item` names `lem-sp-kinjective-comparison-principle`.
- No statement or proof weakening was made; source references and citations remain unchanged.
