Files written:

- `dag/nodes/sec-picard-framework/lem-pc-separable-polynomial-alg-closed-quotient-product.json` — statement, split proof, and blueprint metadata.
- `dag/nodes/sec-picard-framework/lem-pc-separable-polynomial-distinct-roots-alg-closed.json` — statement-only child; no Mathlib exact match.
- `dag/nodes/sec-picard-framework/lem-pc-polynomial-quotient-distinct-linear-crt.json` — statement-only child; no Mathlib exact match.
- `citations.json` — verbatim statement excerpts for every citation.

Attachments: none.

WANTED: none.

The item had no matching declaration in `weil-src-slopmaster2`; the existing node was unsplit. I kept its statement and source, and realized the blueprint clause “factor the separable minimal polynomial after passage to the algebraic closure” by two children. The first child states distinct linear factorization and the exact root count. The second states the evaluation Chinese-remainder isomorphism for pairwise distinct linear factors. The item then composes these facts and identifies the index set with the roots of `P`.

## Review by K1

I read the item node, the `sk-thm-picard-rr` unit record, and the blueprint proof of `lem-pc-ample-positive-degree`. I searched the full DAG, blueprint references, and `weil-src-slopmaster2` for the item tag and for declarations concerning separable polynomial roots, quotient products, and Chinese remainder. No exact Lean declaration or existing DAG statement was found. I also checked the Stacks 00U3 source location recorded by the item and used its two mathematical ingredients directly.

For step 1, the cited child says verbatim that the polynomial factors over `Ω` as the product over its exactly `n` pairwise distinct roots. For step 2, the CRT child says verbatim that evaluation is an `Ω`-algebra isomorphism from the quotient by the product of distinct linear factors to the product of copies of `Ω`; its hypotheses match step 1. Step 3 only reindexes that product by the root set and uses the root count already stated in step 1, so it is elementary. I recorded each citation and exact quote in `citations.json`, and checked the degree-zero case conceptually (empty root set and empty product).
