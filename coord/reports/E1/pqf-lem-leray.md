Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-leray.json` — statement, split; no new nodes or Mathlib leaves.
- `citations.json` — verbatim citations for all proof-step dependencies.

Attachments: none.

WANTED: none.

The imported proof used an informal injective-is-flasque and stalk computation. I replaced that gap with the existing statement `lem-weil-pbc-module-pushforward-injective-acyclic`, which directly supplies the required acyclicity for every open. The existing `thm-sp-grothendieck` statement supplies the spectral sequence, while `pqf-def-cohomology` and `lem-sp-derived-well-defined` supply the derived-functor identifications. No child node was created because each needed fact already exists in the DAG.

## Review by E1

I read the item source blueprint paragraph and the statements of every cited node. Step 1 uses the Grothendieck-category and enough-injectives statement, the abelian-group Grothendieck statement, the module direct-image and global-sections left-exactness statements, the direct-image-of-injectives acyclicity statement, and the composable-acyclic-pair definition; each cited statement explicitly supplies the corresponding hypothesis. Step 2 uses exactly the existence, E2-page, and abutment clauses of `thm-sp-grothendieck`. Step 3 uses the definition of higher direct images and the resolution-independent derived-functor computation, then checks the equality of global sections termwise. I verified that the quasi-coherence hypothesis is harmless because the cited theorem applies to every module, and checked the identity morphism and zero sheaf as small cases. The item statement and displayed indexing agree with Stacks Tag 01F2. The Mathlib searches were run with LeanFinder, Loogle, and grep; they found only generic sheaf/category infrastructure and no Leray declaration.

## Second reading by E1

- Item statement: checked against `cohomology.tex`, Lemma `cohomology-lemma-Leray` (Tag 01F2); the ringed-space bounded-below statement specializes to a scheme and a degree-zero quasi-coherent module with the same E2 indexing and abutment.
- Step 1: checked every cited statement and the actual categories; found the prior étale-module left-exactness citation inapplicable to Zariski `O_X`-modules. Repaired it using `def-pc-module-pullback` and an explicit sectionwise kernel/product argument; acyclicity and Grothendieck hypotheses match.
- Step 2: checked against `thm-sp-grothendieck`; its composable-pair hypotheses and E2/abutment clauses supply exactly this step.
- Step 3: checked `pqf-def-cohomology` and `lem-sp-derived-well-defined`; the derived-functor identifications and section equality give the displayed terms.
- Small cases checked: `f = id`, the zero sheaf, a field spectrum, and total degree `0`.
- No new nodes exist; therefore B1--B7 and duplicate-node checks are vacuous. Mathlib searches remain recorded in the item.
- Changes: replaced the inapplicable étale left-exactness dependency and citation with the scheme-module pushforward definition, added the elementary sectionwise argument, and synchronized `proof_deps`/`tool_uses`.
