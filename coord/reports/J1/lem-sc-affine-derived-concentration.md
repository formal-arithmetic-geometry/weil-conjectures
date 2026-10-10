1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-concentration.json`: item split into three proof steps; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-pushforward-t-exact.json`: new statement-only node; no Mathlib match.

2. Attachments: none. I searched the slopmaster2 source for the item id, its blueprint tag, and the affine derived-pushforward terminology; no sorry-free exact declaration was present.

3. WANTED: `literature/stacks-project/perfect.tex`, Tags 0AVW and 08I8, for `lem-sc-affine-derived-pushforward-t-exact` and the converse step of `lem-sc-affine-derived-concentration`.

4. No statement error was found. The imported item had no proof steps. The split adds the missing affine derived t-exactness/conservativity input rather than treating the converse as an elementary consequence. The existing `lem-pc-affine-morphism-hi` node was reused for the forward direction and the degree-zero identification.

## Review by J1

I read the item node, its blueprint ancestor `lem-sc-finite-duality`, the unit record `sk-thm-picard-duality`, and the neighboring definitions of derived categories and derived direct image. I also read the existing statements of `lem-pc-affine-morphism-hi` and `lem-pc-affine-vanishing`; the former explicitly says that for an affine morphism and a quasi-coherent sheaf, all higher direct images vanish and the ordinary pushforward is quasi-coherent, exactly what Step 1 and Step 3 use. The derived-direct-image definition explicitly identifies the cohomology sheaves of `Rf_*` with the higher direct images, which is cited in both those steps.

For Step 2 I created `lem-sc-affine-derived-pushforward-t-exact` after searching the DAG and blueprint for an existing 08I8 node or equivalent statement. Its statement explicitly supplies t-exactness and reflection of isomorphisms for affine `Rf_*`, so it says the precise converse input rather than merely defining the functor. All three steps have non-elementary uses marked `elementary: false`; their node quotations are copied verbatim into `citations.json`. The item statement still has the original affine, scheme, and quasi-coherent derived-category hypotheses, and the new node introduces the same hypotheses itself.

I checked edge cases conceptually: for the identity affine morphism the equivalence is tautological; for an affine scheme over a point it reduces to the usual equivalence between quasi-coherent sheaves and modules and its derived version; the zero complex and a sheaf in degree zero satisfy both directions. Mathlib searches for the new node used LeanSearch, Loogle, and a pinned Mathlib source grep, with no direct match. No cycles or duplicate blueprint statements were found.
