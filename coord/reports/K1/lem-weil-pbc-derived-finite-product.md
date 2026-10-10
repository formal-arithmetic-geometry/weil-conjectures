# Delivery report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-derived-finite-product.json` (item, statement, split proof)
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-finite-product-injective-resolutions.json` (new statement-only node; no Mathlib match)
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-finite-product-complex-cohomology.json` (new statement-only node; no Mathlib match)
   - `citations.json` (verbatim step citations)

2. Attachments: none. A search of `WeilConjectures/` and `Comparator/` found no declaration tagged `lem-weil-pbc-derived-finite-product` and no matching sorry-free declaration.

3. WANTED: `literature/stacks-project/derived.tex`, Lemma 015M (injective-resolution computation for right derived functors), and `literature/stacks-project/homology.tex` (finite products of complexes); these source files are not present in this checkout. The proof is therefore marked `proof_origin.by = agent` while retaining the cited source locations.

4. No statement error was found. The imported item had no proof; I supplied the componentwise-resolution and componentwise-cohomology argument. The existing `lem-weil-pbc-product-injectives` Mathlib leaf was searched and used only as a generic tool in the new resolution node. The blueprint search for both new statements found no existing equivalent node. The target has no Lean declaration in the source checkout.

## Review by K1

I read the target node, its blueprint ancestor `lem-weil-pbc-zero-dimensional-cohomology`, the unit record `sk-prop-cd`, and the imported neighbouring assembly node. The target statement's hypotheses are exactly the ones used: finiteness of `I` supports the finite product, each `\\mathcal A_i` is abelian with enough injectives, and each `\\Gamma_i` is additive and left exact. Step 1 cites the new product-category statement, whose statement explicitly supplies abelianness, enough injectives, componentwise injectivity, and componentwise injective resolutions; it also cites the definitions that specify injective resolutions and the derived-functor cohomology calculation. Step 2 cites the new finite-product-complex statement, which explicitly gives the natural cohomology isomorphism, and `def-sp-left-exact-additive`, which explicitly identifies each derived functor with the cohomology of the image resolution. The naturality claim follows from coordinate projections and is elementary once that statement is applied.

For both new nodes I searched the whole DAG and blueprint before writing them, then searched LeanSearch/Loogle or LeanFinder and the Mathlib source. Mathlib had only the general product-injectives instance (`CategoryTheory.Injective.instPiObj`), which is recorded on the existing leaf and declared as the item-level generic tool. Neither the product-category resolution theorem nor the finite-product cohomology theorem had an exact Mathlib match, so both new nodes remain statement-only as required. I tested the statements on the empty index set and singleton index set: both reduce respectively to the zero product and the original category/complex. I also checked the two cited definition statements verbatim when preparing `citations.json`; every quote is copied from its node statement.
