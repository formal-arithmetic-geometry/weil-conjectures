1. Files written:
- `dag/nodes/sec-curve-estimates/lem-sc-ample-proj-local-chart.json` (item, repaired split)
- `dag/nodes/sec-curve-estimates/lem-sc-ample-proj-canonical-map.json` (existing child, localization-map clause added)
- `dag/nodes/sec-curve-estimates/lem-sc-affine-global-sections-iso.json` (statement-only Mathlib leaf)
- `citations.json`

2. Attachments: none.

3. WANTED: none.

4. The returned split was wrong because `lem-sc-ample-proj-affine-chart` restated the item's second clause. I deleted it. The canonical-map child now states the additional clause needed by the proof: on each chart the restriction induces `S_(s) -> Gamma(X_s,O)`, `xi/s^n |-> s^(-n) xi`, as in Properties 01PZ (3), Constructions 01N8, and the 01Q1 construction. I added the Mathlib leaf for the final affine criterion; LeanFinder returned `AlgebraicGeometry.instHasAffinePropertyIsomorphismsSchemeAndIsAffineIsIsoCommRingCatAppTop` at `Mathlib/AlgebraicGeometry/Morphisms/IsIso.lean:48`. The item now has five direct proof steps, with proof dependencies equal to their uses.

## Review by M1
I read Properties Definition 01PS, Lemmas 09MP, 01PZ and 01Q1, Coherent Lemma 09MR, Constructions Lemma 01N8, Schemes Lemma 01I1, and the existing statements of every cited DAG node. Step 1 uses the canonical-map statement for existence and the inverse-image identity. Step 2 checks quasi-compactness directly from the ample definition and separatedness from 09MP; quasi-separatedness follows elementarily from separatedness. Step 3 applies 09MR at `p=0`, with `F=O_X` and `L^(tensor d)`, after treating the degree-d section as degree one; the degree-zero Veronese localization is the same `S_(s)` by reindexing. Step 4 uses the definition of Proj for `D_+(s)=Spec S_(s)` and the newly added canonical-map clause to identify the induced ring map. Step 5 applies the affine global-sections criterion, whose Mathlib declaration was read at line 48 and whose hypotheses are exactly affine source, affine target, and an isomorphism on global sections.

I checked the hypotheses on the small cases `X=Spec A, L=O_X` (ordinary principal localization), `X=P^1, L=O(1)` (the two standard charts), and the empty scheme. I also checked that `L=O(-1)` does not satisfy the positive-degree affine cover hypothesis. The requested D1 repair is complete: no child restates the chart-isomorphism conclusion, and the localization argument is in the item's own proof.

## Not duplicates
lem-sc-affine-global-sections-iso vs lem-weil-pbc-spec-z-terminal: the existing node states only that `Spec Z` is terminal, while the new node characterizes an arbitrary affine morphism with an isomorphic global-sections map.
lem-sc-affine-global-sections-iso vs lem-weil-pbc-morphism-into-affine-scheme: the existing node gives the bijection between maps into `Spec R` and ring maps; the new node gives the isomorphism conclusion for a morphism whose induced map is an isomorphism.
lem-sc-affine-global-sections-iso vs lem-weil-pbc-affine-opens-induced-ring-map-spec-square: the existing node identifies a morphism on affine opens with `Spec` of its ring map; the new node concludes that the morphism is an isomorphism when that map is invertible.
lem-sc-affine-global-sections-iso vs lem-weil-pbc-spec-colimit-limit: the existing node concerns limits of affine spectra, not isomorphism detection by global sections.
lem-sc-affine-global-sections-iso vs lem-weil-pbc-spec-map-stalk-localization: the existing node concerns stalks of a `Spec` morphism, not the affine global-sections criterion.
lem-sc-ample-proj-canonical-map vs lem-sc-ample-proj-local-chart: the existing item includes the final ample affine-chart conclusion, while this child only supplies canonical-map existence, inverse images, and the induced localization map used in that conclusion.
