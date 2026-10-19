# Stage-1 report: lem-pur-co-smooth-exchange-transport

1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-co-smooth-exchange-transport.json`: existing item, split into four proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node in every step.

2. Attachments: none.

3. WANTED: none.

4. The imported item had an empty proof. I checked the current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/thm-cbc-finite-level-proetale.proof.md`, which explicitly requires transport of the proper direct-image exchange, transport of both extension-by-zero factors, composition into the compact-support map, and witness independence. I retained the item statement and added those four arguments. The existing item searches were retained; the additional search queries were actually run on 2026-10-17 and recorded in the node. No Mathlib declaration states this site-comparison transport identity.

## Review by NU

I read the item statement and all of its statement dependencies, especially `def-cbc-exchange-map` and `def-exchange-projection`, to verify that the two exchanges are the chosen compactification composites and that no separatedness of the base-change morphism is assumed. I read the blueprint proof lines 4–22 and matched each clause to a proof step. Step 1 cites `lem-weil-pbc-transport-identifies-exchange`, whose statement gives the normalized direct-image transport identity, and `prop-weil-pbc-comparison-direct-image`, whose statement supplies natural comparison isomorphisms compatible with morphisms; `thm-weil-pbc-site-comparison` supplies faithfulness on the bounded-below domain. Step 2 cites `lem-cbc-proetale-extension-zero-comparison` for the etale-to-pro-etale open-extension comparison, `lem-cbc-proetale-extension-zero-base-change` for the pulled-back open square, and `lem-weil-pbc-comparison-pullback` for the canonical pullback comparisons; each cited statement explicitly provides the natural isomorphism used. Step 3 cites the definitions of both compact-support exchanges and the same comparison lemmas, and I checked that composing the proper and open factors gives exactly the displayed equality and remains natural in `L`. Step 4 uses the witness definition and pullback compatibility to justify conjugation by a witness isomorphism and invariance under replacing the witness. I checked the Cartesian square and compactification hypotheses in the definition nodes, and tested the identity-square and identity-open special cases conceptually: every comparison becomes an identity and the displayed equality reduces to reflexivity. No statement was changed, no source error was found, and no new node was necessary.
