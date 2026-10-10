1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ext-one-direct-sum.json`: repaired the item with the explicit direct-sum extension construction and no new nodes.

2. Attachments: none.

3. WANTED: none.

4. The returned version was wrong because its assembly and detection nodes merely restated surjectivity and injectivity (D1). I deleted both nodes and put the omitted argument inside the item. The surjectivity argument now forms the direct-sum map, identifies its kernel, pushes out along the finite-sum map, checks exactness of the quotient extension, and explicitly identifies each pullback with the chosen component extension. The injectivity argument writes every middle-term element as a kernel element plus finitely many pullback elements, then constructs the fixed-end-term isomorphism from the component isomorphisms and its inverse. This addresses D5's omitted-details requirement. No new node was retained, so B4 does not apply.

## Review by F1

I reread the item statement and the proof of Stacks Lemma 05EG in `literature/stacks-project/more-algebra.tex`, lines 24504-24516. The source invokes compatibility of Ext with direct sums but omits precisely the module calculations now written in steps 2-6. I also opened the existing statements of `def-weil-pbc-direct-sum-modules` and `def-weil-pbc-exact-sequence`; each step's citations.json quote is copied from those statements. Step 1 uses the definitions for the pullback and well-definedness. Step 2 uses finite-support decomposition and componentwise exactness to prove surjectivity of the direct-sum map and identify its kernel. Step 3 uses the short-exact-sequence criterion while checking the quotient pushout. Step 4 uses the canonical inclusions and finite support to check the displayed pullback isomorphism and that both endpoint maps are fixed. Step 5 uses finite-support decomposition and surjectivity of each original extension to prove generation of the middle term. Step 6 uses uniqueness of direct-sum components and the fixed-N condition on each $h_j$ to make the glued map well-defined; the inverse is constructed from the $h_j^{-1}$. Step 7 is the elementary set-theoretic conclusion.

I tested the construction on the empty family (the quotient is the unique extension of the zero module) and on a singleton family (the pullback map is the identity), and checked that the signs in the pushout relation make $[(0,\\iota_j u_j(n))]=[(n,0)]$. The two returned clause-sized nodes were removed rather than cited, and proof dependencies now contain only the two existing definitions.

5. Nothing remains unfinished at stage 1.
