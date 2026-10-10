1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-closed-pushforward-abelian-stalks.json`: statement, split proof, no new nodes; Mathlib searches already recorded as partial/no full match.
- `citations.json`: verbatim citations for the module-stalk facts used in steps 1, 2, 4, and 5.

2. Attachments: none.

3. WANTED: none.

4. The item statement was unchanged. I read the item source context in Stacks Sheaves Lemma 00AE and the existing analogous node `lem-weil-pbc-closed-pushforward-stalks`; the latter confirms the six-part stalk argument for modules. I checked `def-weil-pbc-module-stalk` for the directed-neighborhood colimit, germ representatives, germ equality criterion, and functorial stalk maps. Step 1 uses the germ/colimit setup; Step 2 uses germ representatives to restrict to the open complement; Step 3 is the elementary subspace-topology cofinality argument and needs no node; Step 4 uses the stated germ equality criterion and the same colimit; Step 5 uses the stated induced stalk map and preservation of the abelian-group operations. I also checked the empty-subset and whole-space edge cases: the off-subset clause is vacuous for Z=X, while for Z=empty all stalks are zero and the on-subset clause is vacuous.

5. Nothing remains unfinished. No exact sorry-free Lean declaration with the item tag or statement was found in `WeilConjectures`.

## Review by M1

I read the node source and the analogous closed-pushforward module node, then matched each proof step to Lemma 00AE. The only non-elementary inputs are the existing module-stalk facts, and every such citation is present verbatim in `citations.json`. The neighborhood cofinality construction explicitly uses `U union (X\\Z)`, so it applies to the subspace topology without a hidden separation hypothesis. The proof has no circular citation and keeps the original topological-space and abelian-sheaf hypotheses.
