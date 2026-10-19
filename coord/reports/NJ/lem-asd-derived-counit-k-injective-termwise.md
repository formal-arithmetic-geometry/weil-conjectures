# Stage-1 report: lem-asd-derived-counit-k-injective-termwise

1. Files written:

- `dag/nodes/sec-smooth-purity/lem-asd-derived-counit-k-injective-termwise.json` — statement node, split; no new child node and no Mathlib leaf.
- `citations.json` — verbatim statement excerpts for every cited node in every proof step.
- `report.md` — this report.

2. Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its key notions, and the blueprint tag; no sorry-free project declaration states this item exactly. The nearby bounded-below declaration `prop-weil-pbc-derived-inverse-image-adjunction` is narrower (bounded-below abelian sheaves), so it is not an attachment.

3. WANTED: none.

4. Errors or corrections: the imported item statement is well-typed and agrees with the extracted normalization argument. I retained its hypotheses and statement dependencies. The item is strictly smaller than its parent `lem-asd-proper-open-refinement-adjoint-projection`; it supplies only the K-injective counit normalization used in that parent. No child node was needed. The Mathlib searches found only generic derived-adjunction declarations, so `mathlib_match` remains null.

5. Unfinished: nothing in the stage-1 split. No Lean files were written and no compiler, Lake, or build tool was run.

## Not duplicates

- `lem-asd-derived-counit-k-injective-termwise` vs `prop-weil-pbc-derived-inverse-image-adjunction`: the existing node is bounded below and for abelian sheaves, while this item is unbounded and for constant-$R$ module sheaves and gives the K-injective representative formula.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-sc-exact-derived-adjunction-single-counit`: the existing node treats degree-zero objects for arbitrary exact adjunctions; this item treats arbitrary K-injective unbounded complexes and the direct-image resolution computation.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-kun-derived-adjoint-square-comparison`: the existing node compares two derived adjunction squares and does not identify a derived counit with a termwise sheaf counit.

## Review by NJ

I read the current item node, its parent `lem-asd-proper-open-refinement-adjoint-projection`, the `sk-prop-sf-cbc` unit and `sec-smooth-purity` chapter records, and the `main-20261015` blueprint proof for `prop-asd-smooth-base-change`. The blueprint’s coherences (i) and (iii) call for exactly this normalization of a derived counit on a K-injective representative. I also read each cited node statement. Step 1 uses the module inverse-image statement for exactness and the underived adjunction/counit, then uses the termwise derived-inverse-image and exact-functor factorization statements for the comparison. Step 2 checks that the complex is K-injective on the stated source, applies the total-derived K-injective computation, and then uses the unbounded-exchange definition for `Ru_*QI = Q(u_*I)`; the comparison is the one stated by the derived-inverse-image node. Step 3 uses the ordinary unit/counit clauses and the canonical derived adjunction clause, and applies the Stacks Tags 0DVC and 09T5 construction: the adjunct of the identity at `QI`, when the right derived functor is computed by `I`, is the localization of the componentwise ordinary counit. I checked the hypotheses (commutative coefficient ring, scheme morphism, constant-module sheaf categories, exact inverse image, and K-injective complex) against the item statement and the cited statements. Every quote in `citations.json` is copied verbatim from the corresponding node statement. I tested edge cases conceptually (the zero ring, an empty scheme, and a one-term K-injective complex); the formula reduces to the ordinary counit in each case. The four required Mathlib searches were run on 2026-10-18 and their actual results are recorded in the item node.
