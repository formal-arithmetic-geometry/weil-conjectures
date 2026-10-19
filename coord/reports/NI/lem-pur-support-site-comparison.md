## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-support-site-comparison.json`: repaired split statement with eight proof steps.
- `dag/nodes/sec-smooth-purity/lem-pur-derived-support-comparison-direct-image.json`: statement-only node; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-support-quotient-flat.json`: statement-only node; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-support-quotient-product.json`: statement-only node; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-supported-product-quotient-model.json`: statement-only node; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-supported-product-tensor-map.json`: statement-only node; no Mathlib match.
- `citations.json`: verbatim quotations for every current proof-step citation.

## Attachments

None. No sorry-free declaration in the read-only Lean source states the item or any retained new node exactly.

## WANTED

None.

## What was wrong or changed

The returned split had four finer nodes that duplicated proof steps. I removed `lem-pur-support-comparison-restriction-unit` because step 1 is the elementary functoriality of the kernel identity already stated by `lem-pur-derived-support-comparison-direct-image`. I removed `lem-pur-support-quotient-fixed-tensor-model` and `lem-pur-support-quotient-product-comparison`: fixed-$A$ tensor versus constant-ring tensor follows directly from the tensor definition and local constant scalars, while comparison normalization follows directly from the generator-preserving quotient comparison, pullback naturality, and derived tensor comparison. Those arguments are now elementary clauses of step 3. I retained the five genuine smaller lemmas.

All retained worker-node sources now point to the actual blueprint proof file `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-kunneth-supported.proof.md`; no nonexistent “Proof paragraph 4” location is attributed to a Stacks file. I added missing statement dependencies for coefficient categories, sites, schemes, closed immersions, and fibre products. I repaired `lem-pur-supported-product-quotient-model`: its title now matches its statement, the corrupted `\\beta_a` TeX is fixed, the duplicated ending is removed, and the etale map is correctly named `e_a` while the pro-etale map is `q_a`.

## What I could not finish

The five retained technical lemmas are intentionally statement-only and remain unsplit for later stage-1 work.

## Review by NI

I reread the current item statement, all eight proof steps, the five retained node statements, their cited dependency statements, both normalized supported-exterior-product definitions, and blueprint paragraph 4 in the file named above. Step 1 uses the direct-image kernel comparison, the bounded-below comparison unit, canonical pullback restriction, and the global-sections normalization; its restriction and forgetting-supports squares are the elementary functoriality of the same kernel maps. Step 2 uses the free-module Yoneda statement, both extension-by-zero definitions, the comparison direct-image formula, and exact inverse image to identify the quotient generators. Step 3 uses quotient flatness and product multiplication; its fixed-tensor identification and comparison normalization are explicit two-line consequences of the cited tensor definition, generator-preserving quotient comparison, and canonical pullback/tensor naturality. Step 4 constructs the support-kernel adjunction from exact sheafification, K-injective resolutions, and the derived-adjunction interfaces. Step 5 applies composite adjunction and the comparison unit to obtain the counit identity. Step 6 applies canonical pullback/tensor comparison and monoidal coherence. Step 7 uses the quotient-to-pushforward model and the tensor-map lemma, whose statements explicitly identify the normalized counits and transposes. Step 8 compares the two requested maps by their adjunction transposes and substitutes the step-5 counit identity.

I checked every hypothesis: ordinary constant finite-commutative-ring modules, small etale/pro-etale sites, separated finite-type schemes over an algebraically closed field, closed supports, bounded-below coefficient complexes where the comparison unit is inverted, and unbounded derived support adjunctions where required. I tested empty and full supports, empty schemes, the zero ring, and nonreduced supports. I checked every citation quote in `citations.json` is copied verbatim from the current cited statement. I searched the DAG and blueprint for duplicates and recorded the distinctions below. The retained Mathlib search records are the actual LeanSearch, Loogle, LeanFinder, and Mathlib-grep results from the prior attempt; no search was fabricated or rerun for an unchanged query.

## Not duplicates

- `lem-pur-derived-support-comparison-direct-image` vs `sk-prop-sf-comparison`: the new node is the unbounded supported-kernel comparison for arbitrary pro-etale complexes; the existing node is bounded-below comparison for etale-origin coefficients.
- `lem-pur-support-quotient-flat` vs `lem-pur-supported-affine-line-homotopy`: the new node proves flatness and K-flatness of the closed-support quotient; the existing node proves affine-line invariance of supported cohomology.
- `lem-pur-support-quotient-product` vs `lem-pur-supported-product-localization`: the new node identifies product support quotients by generator multiplication; the existing node concerns localization triangles for supported exterior products.
- `lem-pur-supported-product-quotient-model` vs `lem-pur-support-site-comparison`: the new node identifies quotient and closed-pushforward support models within one topology; the item compares etale and pro-etale supported exterior products.
- `lem-pur-supported-product-tensor-map` vs `def-pur-supported-exterior-product`: the new node proves the quotient-model tensor map is the normalized exterior-product map; the existing node defines the etale exterior-product construction.
