# Stage 1 report: def-sp-etale-dictionary

## Files written

- dag/nodes/sec-picard-framework/def-sp-etale-dictionary.json
- coord/reports/E1/def-sp-etale-dictionary.md

## Split

I read the single paragraph of the blueprint node (order 598) and the unit
sk-def-groth-ss. This is a definition of substitutions, so it has no proof
steps or new nodes. Its statement now cites the existing definitions for
etale sheaves, direct image, bounded-below derived categories, derived inverse
image, derived exchange, and composable pairs. The four imported dependencies
remain.

The blueprint identified a bounded-below complex with an object of the
derived category. The corrected wording says the complex represents that
object. It also called the exchange morphism a transformation of couples;
the corrected wording leaves compatibility with the couple structure to the
separate couple-morphism statement. These changes make the substitutions
well-typed without changing the route of the unit.

## Attachments and sources

No exact declaration tagged def-sp-etale-dictionary or stating the whole
dictionary was found in
/home/ubuntu/weil-src-slopmaster2/WeilConjectures. The source has the
individual etale and derived constructions, but no single declaration for
this cross-chapter dictionary. No attachment or new node is proposed.

The item has LeanSearch, Loogle, and Mathlib-source grep searches. They find
sheaf pushforward and site constructions, but no declaration for the whole
dictionary. No document is wanted. No Lean was written or built.

## Review by E1

I read the sk-def-groth-ss unit's etale-substitution sentence and the original imported blueprint paragraph retained in the node's prior revision. They list the abelian etale-sheaf category, f_* and its derived functors, bounded-below complexes, derived inverse images, exchange and the composable pair. The revised node still states those substitutions. I checked the statements of the cited definitions: def-weil-pbc-derived-categories distinguishes a complex from its image in D+, def-sp-kinjective-bridge computes derived direct image on a K-injective resolution, and def-weil-pbc-derived-exchange defines a natural transformation g^-1 Rf_* -> Rf'_* g'^-1. Thus the two worker corrections repair actual type and role errors: the complex represents K, and compatibility of exchange with exact couples is left to its separate lemma. The remaining cited definition nodes introduce the site, sheaf category, direct image, inverse image and composable pair used here.

This is a definition with no proof or new node, so B1-B9 and C-D impose no new-node or proof-step checks; its references were searched through the full blueprint and slopmaster2, with no single exact declaration to attach. The empty-site case does not alter the category or functor substitutions. The worker's second source/citation pass found no additional repair, and I found no A-E defect. The revised statement is a clarification of the imported dictionary, not a change to a target.
