## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-r-lim-levelwise-isomorphism.json` — item, statement node; no new node and no Mathlib leaf.
- `citations.json` — verbatim citations for the sole proof step.

## Attachments

None. I searched the project source for the blueprint tag, item wording, and the relevant derived-limit terms; no sorry-free declaration states this item.

## WANTED

None.

## What was wrong or incomplete

The imported proof had an unnumbered paragraph with `uses: []` and `elementary: null`, despite relying on the derived-limit definition and the non-elementary fact that a morphism of Roos triangles with isomorphic middle terms has an isomorphic first term. The existing node `lem-weil-derived-limit-levelwise-iso` states that latter fact exactly, so I cited it rather than creating a duplicate child. The item’s original `stmt_deps` omitted this required statement dependency.

## What I could not finish

Nothing; this is a DAG-only stage-1 split.

## Review by NF

I read the item source file and the complete master blueprint paragraph at `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-r-lim-levelwise-isomorphism.md`, and checked the chapter and unit records. I read the full statements of `def-weil-pbc-adic-derived-inverse-limit` and `lem-weil-derived-limit-levelwise-iso` in the DAG. Step 1 uses the definition’s explicit clause that maps of towers act componentwise on the two products and hence on the cone; this supplies the Roos-triangle morphism. It then uses the existing levelwise-isomorphism statement, whose hypotheses explicitly require a morphism of inverse systems with every component an isomorphism and a morphism of Roos triangles, and whose conclusion is that the induced derived-limit map is an isomorphism. Thus every cited quote is verbatim and every non-elementary fact is cited. I verified the original item’s hypothesis and conclusion are preserved exactly, and corrected the missing dependency, incomplete proof metadata, null elementary flag, and absent Mathlib search records. The item is a direct specialization of the existing node, so no new node was warranted.

## Second reading by NF

- Item statement: checked the blueprint node and its proof against the complete source paragraph; the compatible tower map and levelwise-isomorphism conclusion, including empty/zero towers and the cases $n=0,1$, are unchanged.
- Step 1: checked the componentwise product and cone construction against `def-weil-pbc-adic-derived-inverse-limit`, and the morphism-of-Roos-triangles and isomorphism conclusion against the complete statement of `lem-weil-derived-limit-levelwise-iso`; the step's non-elementary uses are both cited and its elementary flag is false.
- New nodes: none; the existing `lem-weil-derived-limit-levelwise-iso` was searched for and cited, so no duplicate or Mathlib leaf is introduced.
- Definitions and edge cases: checked the tower, products, shift, cone, and derived-limit terminology against their definition nodes; the zero object and field cases are vacuous/special cases of the same statement.

Changes made: preserved the imported item's required null blueprint ancestor, replaced both citation quotes with the full verbatim statements of their cited nodes, and recorded this second-reading audit. No mathematical statement or proof step was changed.
