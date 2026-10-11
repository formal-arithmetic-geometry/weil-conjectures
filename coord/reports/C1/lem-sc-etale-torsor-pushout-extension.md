Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-etale-torsor-pushout-extension.json`: item split; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every step.

Attachments: none.

WANTED: none.

The item was not already stated by a sorry-free project declaration. I read the item source, Stacks Cohomology on Sites Lemma 03AJ, and checked the existing statements of `def-weil-pbc-abelian-etale-sheaves`, `lem-weil-pbc-pushout-short-exact-sequence`, and `lem-sc-abelian-sheaf-short-exact-stalkwise`. Step 1 uses the abelian-category hypothesis and the generic pushout exactness conclusion exactly as stated. Step 2 uses the stalkwise exactness criterion to justify local representatives and the quotient relation in the fibre. Step 3 uses the same criterion for local lifts and uniqueness modulo the kernel, then identifies the induced action with the second-factor action. The hypotheses are the small etale site of a scheme, a morphism of abelian sheaves, and the canonical short exact torsor extension; all are present in the item statement or cited definitions. I checked the identity morphism case, where the pushout and contracted product reduce to the original extension and torsor, and the zero target case, where the fibre is a singleton. No source or statement error was found.

## Review by C1

I read the complete item JSON and the three cited node statements. The generic pushout node supplies exactness in an arbitrary abelian category, and the étale-sheaf definition supplies that category; the stalkwise node supplies precisely the local-surjectivity and kernel-difference facts used in Steps 2 and 3. No step relies on a cited node's proof or on an unstated construction. The new split has no new nodes, so there are no duplicate or Mathlib-leaf statements to review. The three Mathlib searches were rerun with the item id and recorded as executed; they found only unrelated categorical pushout/pullback declarations. Small cases (identity coefficient map and zero target) agree with the statement.

## Second reading by C1

- Item statement: checked against Stacks Cohomology on Sites, Lemma 03AJ (label `lemma-torsors-h1`); verdict: hypotheses and pushout/fibre conclusion agree, including identity and zero-target cases.
- Step 1: checked against the abelian-sheaf category and generic pushout exactness statements; verdict: cited statements say exactly what is used.
- Step 2: checked against `lem-sc-torsor-h1`'s formal-generator construction and the stalkwise pushout facts; verdict: the local representative reduction and quotient relation are now explicit and cited.
- Step 3: checked against stalkwise short exactness and the torsor definition; verdict: local lifting, uniqueness modulo the kernel, and the action identification are explicit.
- New nodes: none; B1-B7 and duplicate/Mathlib-node checks were not applicable.
- Changes: added `lem-sc-torsor-h1` to Step 2 and `proof_deps`, and added its verbatim statement quote to `citations.json`; the prior step used the formal-generator reduction without citing its defining node.
