# Worker report

1. Files written: the item `dag/nodes/sec-trace-formula/lem-trf-topos-complement-module-stalks.json`; no new nodes (all four supporting facts already exist and are cited). The item is a split statement, with no Mathlib leaf.
2. Attachments: no Lean declaration attaches to this item. Existing supporting nodes used are `lem-pe-constant-left-module-inverse-image`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-trf-oriented-closed-base-localization`, and `lem-trf-topos-complement-factorization`.
3. WANTED: none.
4. No statement or blueprint correction was needed. The source statement is the module enhancement of Stacks Tags 03DI, 0710 and 04EQ together with the complementary-subtopos results in Tags 08LY and 08M1. The item had been unsplit and its imported proof was empty; I supplied the proof steps and added the missing proof dependencies.
5. Nothing remains unfinished.

## Not duplicates

`lem-trf-topos-complement-module-stalks` vs `lem-trf-oriented-closed-base-localization`: the existing node gives the closed-subtopos support and module direct-image theorem, while this item additionally states open extension-by-zero, point dichotomy, all four point stalk formulas, unit/counit identities, and exact point inverse images.

`lem-trf-topos-complement-module-stalks` vs `lem-pur-site-restriction-module-adjunction-exact`: the existing node is only the site-local restriction/extension adjunction and exactness; this item treats complementary open and closed geometric embeddings and point behavior.

`lem-trf-topos-complement-module-stalks` vs `lem-pe-constant-left-module-inverse-image`: the existing node only proves exact module inverse image for constant rings; this item includes the open/closed adjunctions, support, factorization, stalk formulas, and units/counits.

## Review by NS

I read the item source in `literature/stacks-project/sites-modules.tex` at Tags 03DI, 0710 and 04EQ, and the closed-subtopos source in `literature/stacks-project/sites.tex` at Tags 08LY and 08M1. I also opened the complete statements of every cited DAG node. Step 1 uses exactly the statement of `lem-pe-constant-left-module-inverse-image`: inverse image transports the constant scalar action and is exact. Step 2 uses the exact restriction and module extension-by-zero adjunction in `lem-pur-site-restriction-module-adjunction-exact`; the slice is the open subtopos defined by u. Step 3 uses the exact, fully faithful closed direct image and its support characterization from `lem-trf-oriented-closed-base-localization`. Step 4 uses the universal factorization clauses of `lem-trf-topos-complement-factorization`; the only additional observation is the elementary fact that a subterminal set is empty or singleton. Steps 5 and 6 use the same factorization and closed-support statements; the point formulas and identities are the direct stalk calculation of Tags 0710 and 04EQ, with zero on the complementary side and the identity on the relevant side. Step 7 reuses the exact inverse-image statement, and step 8 checks the degenerate cases u=0, u=1 and the zero ring against those same statements.

I checked the hypotheses: all module categories use the constant sheaf of the same commutative ring Λ; j is the slice geometric morphism of the given subterminal u; k is the complementary closed embedding supplied by the factorization node; and p is a geometric point, so p^{-1}u is a subterminal object of Set. I tested the edge cases u=0 (the open slice is the whole topos and the closed complement is empty), u=1 (the reverse), and Λ=0 (all module categories are zero). The existing closed-complement node is deliberately recorded as a generic tool use because it supplies the closed module support theorem that the source-localization route treats as a black box. No SGA source is used.
