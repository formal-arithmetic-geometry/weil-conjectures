1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-etale-torsor-h1-functoriality.json` (statement, split, no Mathlib match)
- `dag/nodes/sec-curve-estimates/lem-sc-etale-torsor-inverse-image-extension.json` (statement-only supporting node, no Mathlib match)
- `dag/nodes/sec-curve-estimates/lem-sc-etale-torsor-pushout-extension.json` (statement-only supporting node, no Mathlib match)

2. Attachments: none.

3. WANTED: none; the cited Stacks source is represented by the project's imported literature path.

4. The original item was statement-only and had only a broad Mathlib grep. I searched the DAG and blueprint for both supporting facts; neither was duplicated. The proof now follows Stacks Cohomology on Sites, Lemma 03AJ: representative extension, inverse-image compatibility, pushout compatibility, and naturality of connecting classes. The two new nodes are strictly smaller than the item and do not restate either conclusion clause. Mathlib searches were run for each new node and the item with LeanFinder, Loogle, and Mathlib grep; all found no relevant sheaf-torsor declaration.

## Review by C1

I read the item source description and the neighboring Zariski nodes. The item hypotheses explicitly use small étale sites, so the Zariski functoriality node was not reused. Step 1 uses the canonical torsor-to-extension representative from `lem-sc-torsor-h1` and the inverse-image extension statement; these state exactly the fibre and pulled-back extension used. Step 2 uses the functoriality node's naturality clause and the representative description of `lem-sc-torsor-h1`, yielding the class of `u^{-1}T`. Step 3 uses the same representative description and the new pushout statement, whose hypotheses include an abelian coefficient morphism and whose conclusion gives the contracted-product fibre. Step 4 uses the coefficient naturality clause and the same pushout and representative statements. Every citation quote is copied verbatim from the cited node statement. I checked the identity-coefficient and one-point cases: inverse image preserves the trivial torsor, and for `phi = id` the pushout fibre is the original torsor. No hypotheses beyond those stated in the item are used.

## Not duplicates

lem-sc-etale-torsor-inverse-image-extension vs lem-sc-etale-torsor-h1-functoriality: the new node is the representative-extension compatibility `u^{-1}E_T = E_{u^{-1}T}` and does not assert the induced H^1 class map; the item asserts the full pullback conclusion.
lem-sc-etale-torsor-pushout-extension vs lem-sc-etale-torsor-h1-functoriality: the new node is the extension-level pushout and fibre calculation, while the item additionally asserts the induced H^1 coefficient map sends classes to contracted products.
lem-sc-etale-torsor-inverse-image-extension vs lem-weil-pbc-gabber-h1-absolutely-algebraically-closed: the existing node concerns vanishing/injectivity of H^1 over absolutely algebraically closed fields, not functoriality of the canonical torsor extension under an arbitrary scheme morphism.
lem-sc-etale-torsor-pushout-extension vs lem-weil-pbc-gabber-h1-absolutely-algebraically-closed: the existing node has no coefficient pushout or contracted-product torsor statement; the new node is the general extension-level pushout calculation.

## Second reading by C1

- Step 1 checked against Stacks tag 03AJ / label `lemma-torsors-h1`, [lem-sc-torsor-h1], and the inverse-image extension node; the pulled-back exact sequence and fibre identification match the stated hypotheses.
- Step 2 checked against the naturality clause of [lem-weil-pbc-cohomology-pullback-functorial] and the boundary representative in [lem-sc-torsor-h1]; the class calculation is correctly stated.
- Step 3 checked against tag 03AJ and the pushout-extension node; the coefficient morphism, exact pushout, and contracted-product fibre are all in force.
- Step 4 checked against coefficient naturality and the same pushout and boundary descriptions; it derives the induced H1 map without adding hypotheses.
- Node `lem-sc-etale-torsor-h1-functoriality` checked clause by clause against tag 03AJ and the cited definition nodes; pullback and coefficient-change conclusions are distinct and correctly scoped.
- Node `lem-sc-etale-torsor-inverse-image-extension` checked against tag 03AJ; it is a strict representative-extension compatibility fact, not the item’s H1 conclusion.
- Node `lem-sc-etale-torsor-pushout-extension` checked against tag 03AJ and the explicit contracted-product action; it is a strict extension-level fact, not the item’s induced-map conclusion.
- Small cases checked: zero/trivial torsor, identity coefficient map, one-point scheme, and empty scheme; all clauses reduce to the expected trivial or initial sheaf cases.

Changes: made all three Stacks source places name label `lemma-torsors-h1`; replaced the item’s search metadata with the actual second-reader `msearch.py` results; recorded this audit.
