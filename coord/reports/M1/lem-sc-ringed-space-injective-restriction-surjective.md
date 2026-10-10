1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-ringed-space-injective-restriction-surjective.json` (item, split, no new nodes, no Mathlib leaf).
- `citations.json` (verbatim statement excerpts for every cited step).

2. Attachments: none.

3. WANTED: none.

4. The imported item had the correct Stacks 01EA statement but no proof. I found no sorry-free declaration in `WeilConjectures/` stating it exactly. The proof now follows the source: extension by zero represents sections, the nested-open extension map is a monomorphism by its stalk formula and stalkwise exactness, injectivity gives the surjective Hom map, and the two-open difference map follows by taking one lift and zero. No statement was weakened or changed. The proof uses the existing arbitrary-ringed-space adjunction node and the existing topological extension-by-zero stalk node; the scheme-only module extension node is not used.

5. What I could not finish: nothing.

## Not duplicates

`lem-sc-ringed-space-injective-restriction-surjective` vs `lem-sc-derived-open-restriction-adjunction-exact`: the existing node states existence, exactness, and adjunction of extension by zero for one open; this item proves surjectivity of sections for an injective object across two nested opens and the induced difference map.

`lem-sc-ringed-space-injective-restriction-surjective` vs `lem-sc-ext-coherent-hom-injective-flasque`: the existing node is a Noetherian-scheme/coherent-module internal-Hom flasqueness specialization; this item is the general ringed-space injective-module restriction lemma.

`lem-sc-ringed-space-injective-restriction-surjective` vs `lem-weil-pbc-module-open-restriction-injectives`: the existing node concerns preservation of injectivity after restricting a scheme module to one open; this item concerns surjectivity of sections of an injective on nested opens.

## Review by M1

I read `/home/ubuntu/c1-stacks-review/cohomology.tex`, Cohomology Lemma 01EA (`lemma-injective-restriction-surjective`), including its full proof, and the cited DAG statements. Step 1 uses `lem-sc-derived-open-restriction-adjunction-exact`, whose adjunction clause gives the Hom bijection and naturality; the structure-sheaf Hom-to-sections identification is elementary. Step 2 uses `lem-sc-topological-extension-by-zero-stalks` for the underlying abelian stalk calculation and `lem-weil-pbc-module-stalk-exact` (5) for the stalkwise monomorphism criterion; the module sheafification construction and its underlying abelian sheaf are stated in the cited adjunction node. Step 3 uses `def-sp-injective-resolutions` and the same adjunction node. Step 4 is elementary: choose a lift on one open and zero on the other.

## Second reading by M1

- Item statement: checked against Cohomology 01EA; hypotheses and both conclusions agree. Edge cases U'=U, U'=empty, U=V=X, and I=0 were checked.
- Step 1: checked against `lem-sc-derived-open-restriction-adjunction-exact`; the structure-sheaf Hom-to-sections identification is elementary.
- Step 2: checked against `lem-sc-topological-extension-by-zero-stalks` and `lem-weil-pbc-module-stalk-exact` (5); stalk maps are identity on U' and zero outside.
- Step 3: checked against `def-sp-injective-resolutions` and the cited adjunction; no scheme hypothesis is used.
- Step 4: checked directly from Step 3; one lift and zero gives the difference-map surjection.
- New nodes: none; B1-B7 and duplicate/new-node checks are vacuous. The scheme-only extension node was removed from all dependencies.
- Mathlib searches: the node records the three executed searches and the unavailable LeanSearch result exactly as in `searches.jsonl`.

Changes: replaced the scheme-only extension citation with arbitrary-ringed-space adjunction and topological stalk nodes, removed an unused dependency, corrected metadata, and synchronized citations and searches.

I checked the small cases `U'=U` (the restriction is the identity), `U'=empty` (the target section group is zero), `U=V=X` (the difference map is plainly surjective), and the zero module. The source, item hypotheses, and all cited statements agree. The existing node and DAG were searched for the Stacks tag and for extension-by-zero/injective restriction keywords; no duplicate statement of this general result was found. Mathlib searches were run with the required launcher commands: LeanFinder `sections of injective sheaf over U plus V surject onto intersection` (generic stalk-injectivity hits, no ringed-space theorem), Loogle `Sheaf sections surjective injective flasque` (no hits; unknown identifier), grep `injective.*flasque|surjective.*U.*V` in Mathlib (no hits), and LeanSearch `restriction map on sections of an injective sheaf over nested opens is surjective` (service unavailable, recorded as unavailable). The imported item's existing three searches were also retained unchanged.
