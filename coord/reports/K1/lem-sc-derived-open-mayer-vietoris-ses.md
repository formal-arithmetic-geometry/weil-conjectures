Files written:

- `lem-sc-derived-open-mayer-vietoris-ses.json` — item, statement split into three proof steps; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement quotes for every cited node in every step.

Attachments:

- None.

WANTED:

- None; Stacks source `literature/stacks-project/cohomology.tex` is available.

What was checked or corrected:

- The source is Stacks Tag 08BU, label `cohomology-lemma-exact-sequence-lower-shriek`, whose proof takes a representative complex and checks the degreewise extension-by-zero sequence on stalks. The item is the underlying sheaf-module short exact sequence, so its statement was retained.
- Existing DAG searches found no duplicate statement or blueprint node for this SES. The existing `lem-sc-topological-extension-by-zero-stalks` gives the stalk formula needed for modules after forgetting to abelian sheaves; `lem-weil-pbc-module-stalk-exact` gives exactness iff stalkwise exactness; `def-weil-pbc-exact-sequence` gives the short-exact conclusion. Therefore no child node was created.
- Step 1 explicitly defines the difference and counit maps and checks their composite is zero. It uses only the existing exact extension-by-zero/adjunction statement and the module definition.
- Step 2 checks all four point cases (`U∩V`, `U\\V`, `V\\U`, and the complement), giving the exact stalk complexes and direct module calculations. The cited stalk formula says the extension stalk is the original stalk on the open and zero outside.
- Step 3 applies the cited stalkwise exactness criterion and the definition of short exact sequence. All cited statements were opened and the quotation strings in `citations.json` were copied verbatim.
- Small cases checked: `U=X`, `V=∅` gives the identity sequence; `U=V=X` gives `0→F→F⊕F→F→0`; and disjoint opens give zero intersection and componentwise identity maps.

## Review by K1

I read the complete Tag 08BU source proof in `cohomology.tex` around `lemma-exact-sequence-lower-shriek`, including its explicit statement that exactness is checked on stalks using the extension-by-zero stalk lemma. I also read the statements of every cited DAG node. The first step uses the exact extension-by-zero adjunction node only for the available functor and counits, and the sheaf-of-modules definition for linearity. The second step uses the topological extension-by-zero stalk formula exactly as stated, with the module stalk definition for the pointwise calculations; each of the four cases was checked. The third step uses the module stalk exactness criterion exactly as stated, then the short-exact definition. I checked the edge cases listed above and found no extra hypothesis beyond a ringed space and an open two-set cover. No correction to the mathematical statement was needed; the proof was added because the imported item had no proof.

## Second reading by K1

- Item statement: checked against Stacks Tag 08BU, label `lemma-unbounded-mayer-vietoris`, including the ringed-space and two-open-cover hypotheses; the SES is the one used in its proof.
- Steps 1-3: checked against Tag 08BU and every cited DAG statement; maps, four stalk cases, and stalkwise exactness conclusion are correct, with elementary markings justified.
- New nodes: none; existing-node and Mathlib searches were checked.
- Corrected all source metadata from the nonexistent label `cohomology-lemma-exact-sequence-lower-shriek` to `.tex` label `lemma-unbounded-mayer-vietoris`, and corrected the stalk citation to Sheaves Lemma 6.31.8.
- Edge cases $U=X$, $V=\\varnothing$, $U=V=X$, disjoint opens, and the empty space were checked.
