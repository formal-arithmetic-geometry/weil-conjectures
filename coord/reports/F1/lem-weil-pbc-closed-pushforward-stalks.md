1. Files written

- Item: `dag/nodes/sec-proper-base-change/lem-weil-pbc-closed-pushforward-stalks.json`; status set to `split`, with six proof steps and proof dependencies.
- New nodes: none. The existing Mathlib searches are retained: `stalkPushforward_iso_of_isInducing` covers the bijectivity half of (2), while the off-image vanishing and module linearity are not present in Mathlib.

2. What changed

- Split the Stacks Lemma 00AE argument into: pushforward/germ notation; vanishing off the closed image; cofinality of neighbourhoods over `i(z)`; the induced bijection of stalk colimits; `O_{X,i(z)}`-linearity through `i^sharp_z`; and naturality in the module.
- The proof dependencies are existing definitions only: `def-pc-scheme`, `def-weil-closed-immersion`, `def-pc-module-pullback`, and `def-weil-pbc-module-stalk`.
- No Lean writing or compilation was performed, as required for Stage 1.

3. Source review

- The statement matches Sheaves Lemma 00AE for sheaves of abelian groups/modules, with the additional linearity calculation used in Modules Lemma 08KS.
- The cofinality argument explicitly extends an open `U` with `Z cap U` equal to a chosen neighbourhood by adjoining `X \\ i(Z)`, so the same section-colimit identification used by 00AE is available for the scheme morphism formulation.
- The germ multiplication calculation gives the stated `O_X`-linearity, and functoriality of restrictions gives naturality.

## Review by F1

I checked all six steps against the cited Stacks proof and the cited nodes. The off-image case uses the open complement of the closed image and zero sections on the empty open; the on-image case uses exactly the neighbourhood cofinality in 00AE. The linearity step correctly uses the `i^sharp_z` action on the target stalk, and the naturality square commutes on every germ representative. No statement error, duplicate node, or route departure was found. `review_split.py` passes; no new node requires additional search or citation.
