1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-functor-termwise-split-ses-triangle.json` — statement, three proof steps, no new nodes, Mathlib searches recorded as no match (LeanSearch unavailable).
- `citations.json` — verbatim statement quotes for every cited node in every proof step.
- `report.md` — this report.

2. Attachments: none. No sorry-free project declaration matching the item was found under `WeilConjectures/`.

3. WANTED: none.

4. What was wrong or incomplete: the imported item had an empty proof despite being used by the Mayer--Vietoris functoriality node. The Mathlib searches found generic K-injective and exact-functor declarations but no theorem identifying the connecting morphism for a termwise split sequence under a right-derived functor. I retained the item's statement and split its argument without introducing duplicate child nodes; all needed generic triangle, splitting, and K-injective facts already exist in the DAG.

5. Nothing remains unfinished.

## Review by J1

I read the target node, its `sec-picard-framework` chapter and `sk-thm-picard-semicon` unit records, and the downstream use in `lem-pc-derived-mayer-vietoris-functorial`. I searched the slopmaster2 Lean source by the item id, terminology, and blueprint tags; there is no matching declaration, so this is not an attachment. I also ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; the first three gave only generic results and LeanSearch was unavailable, all recorded in the node.

For Step 1 I checked the exact statements of `def-sp-left-exact-additive`, `lem-weil-pbc-degreewise-split-connecting-morphism`, `lem-weil-pbc-degreewise-split-derived-triangle`, and `lem-weil-pbc-complex-ses-triangle`. They provide additive preservation of the splitting identities, the explicit degreewise connecting formula, and the distinguished triangle for the image short exact sequence. For Step 2 I read `def-pur-kinjective-complex`, `def-pc-derived-direct-image`, `lem-pc-right-derived-functor-triangulated`, and the short-exact triangle node; their hypotheses match the K-injective representatives and their conclusions give represented-complex computation and preservation of distinguished triangles. For Step 3 I reread the splitting formula and triangle naturality statements and verified that applying the additive functor preserves the compositions, identities, differential, and sign convention, so the image connecting map is the one obtained by applying RF.

I checked every citation quote programmatically against the source node statements and checked that `proof_deps` is exactly the union of the step uses. The only correction during review was replacing plain Unicode arrows and prose formulas with the project's TeX notation; no mathematical hypothesis was added or dropped.

## Second reading by J1

- Item statement: checked against the existing derived-category and K-injective definitions and the stated Stacks Lemma 0152 route; verdict: retained, with the represented-complex interpretation made explicit by cited nodes.
- Step 1: checked the additive splitting identities against `def-sp-left-exact-additive`, `lem-weil-pbc-degreewise-split-connecting-morphism`, and the distinguished-triangle nodes; verdict: the termwise split argument is supported.
- Step 2: checked K-injective computation and triangulated preservation against `def-pur-kinjective-complex`, `def-pc-ringed-spaces-derived-direct-image`, `lem-pc-right-derived-functor-triangulated`, and `lem-weil-pbc-complex-ses-triangle`; verdict: the generic ringed-space construction is the correct citation for an abstract functor.
- Step 3: checked the formula and shift sign against `lem-weil-pbc-degreewise-split-connecting-morphism` and `lem-weil-pbc-degreewise-split-derived-triangle`; verdict: the displayed representative is exactly the image connecting morphism.
- New nodes: none; the argument uses existing nodes only, and the recorded Mathlib searches were checked for query/result consistency.
- Changed the item metadata `created.item` to the delivered item so preflight recognizes ownership.
- Replaced the scheme-specific derived direct-image citation with the generic ringed-space K-injective construction and updated its verbatim citation quote and dependencies.
