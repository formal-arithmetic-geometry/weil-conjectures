Files written:

- `dag/nodes/sec-nagata-compactification/def-nagata-final-descended-model.json` (definition, split; no new nodes)
- `citations.json` (empty because definitions have no proof steps)

Attachments: none.

WANTED: none.

The source blueprint marks this intermediate choice-definition as bypassed by the direct formalized route through `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`; no exact declaration with the definition's named objects exists in the project source. I retained the imported statement and split it against its existing dependencies rather than inventing a theorem or child node.

## Review by K1

I read the item's blueprint note and the unit proof in `dag/units/sk-cor-nagata-sketch-fp.json`, together with `dag/notes/sec-nagata-compactification/explicit-final-assembly--remark-1.json`. That note says the named descended model and its later compactification objects are collapsed into the direct Nagata theorem. I also read each cited dependency: `def-nagata-final-noetherian-base-system` defines the system `N(S)` and its limit comparison; `def-nagata-separated-descent-stage` defines the selected separated stage and model; and `lemma-nagata-final-noetherian-base-system` supplies the constructed approximation system. These statements provide exactly the objects used by the item's definition. Since the item is a definition, it has no proof steps or non-elementary citations, so `citations.json` is intentionally empty.

I searched the whole DAG and blueprint for the definition's distinctive terms and found only this node and the dependent final-assembly nodes; the related definitions are distinct constructions. I searched the project source for the item id, `lambda_sep`, and the named descended-model notation and found no matching declaration; the available Lean theorem uses direct existential data instead. The definition was checked structurally so every introduced symbol is supplied by a stated dependency and no proof claim is hidden in the definition.
## Second reading by K1

- Item statement: checked the imported blueprint node at order 373 and the final-assembly note; the qcqs base, separated finite-presentation morphism, selected index/model, and comparison map agree, including zero, field, and empty-base edge cases.
- `def-nagata-final-descended-model`: checked as a statement-only definition (B1), with each displayed notion tied to existing base-system/descent dependencies (B2-B3); no proof step or citation quote is required.
- Dependency audit: read `def-nagata-final-noetherian-base-system`, `def-nagata-separated-descent-stage`, and `lemma-nagata-separated-descent-stage-exists`; the last statement supplies the canonical base-change comparison used by `epsilon_Y`.
- Existing-node search: searched the DAG for `lambda_sep`, `Y^{\\mathrm{sep}}`, and the comparison notation; no duplicate definition node was found. Mathlib search records were retained because this bypassed definition has no new theorem node.
- Changed the wording from “constructed base-change comparison” to “canonical base-change comparison supplied by the separated-descent existence statement” and added `lemma-nagata-separated-descent-stage-exists` to `stmt_deps`, so the introduced map has an explicit dependency.
