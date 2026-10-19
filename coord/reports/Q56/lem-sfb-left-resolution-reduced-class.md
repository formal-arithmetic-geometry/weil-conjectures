Files written:

- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-reduced-class.json`: statement node, split; proof has two steps and uses two new Mathlib leaves plus `def-sp-abelian`.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-reduced-api.json`: statement node, Mathlib leaf (`CategoryTheory.Abelian.LeftResolution.reduced` and its zero-preservation instance).
- `dag/nodes/sec-proetale-coefficients/lem-sfb-abelian-idempotent-complete.json`: statement node, Mathlib leaf (`CategoryTheory.Idempotents.isIdempotentComplete_of_abelian`).

Attachments: none.

WANTED: none.

The imported item statement is unchanged. I found no finished project declaration carrying the blueprint tag, and no existing DAG node states either new Mathlib fact. The full-subcategory packaging is part of the item's proof rather than a separate clause node. The two new nodes have no Stacks tags and therefore no duplicate pair to report.

## Review by Q56

I read the item node, the unit `sk-def-sfb-derived-tensor-hom`, the chapter record, and the blueprint proof `lem-sfb-derived-monoidal.proof.md`. I also read Mathlib `Algebra/Homology/LeftResolution/Reduced.lean` lines 105–129 and `CategoryTheory/Idempotents/Basic.lean` around the abelian idempotent-completeness instance. The reduced API node records exactly the construction and the immediately following zero-preservation instance; the abelian leaf records the ambient splitting fact.

Step 1 defines C as the full subcategory on F. I checked the hypotheses one by one: `def-sp-abelian` supplies the preadditive structure, zero object, and finite biproducts of A; containment of zero and closure under finite biproducts supply the corresponding structures in C; fullness gives the additive fully faithful inclusion. The cited idempotent-completeness statement applies to A. For an idempotent in C, its splitting in A has a retract object that is a direct summand of an F-object, hence is in F; fullness puts both splitting maps in C. This verifies the extra hypothesis needed by the reduced construction.

Step 2 regards P, whose values lie in F, as a functor Q0 into C and epsilon as the required natural epimorphism, so it forms a LeftResolution. I checked that no additivity or zero-preservation of the original P is assumed. Applying the cited reduced API yields Q with zero-preserving morphism action and pi with epimorphic components, while the definition of C gives iota(X) in F. This matches every conclusion of the item.

No statement dispute or proof gap remains. The Mathlib searches for both new leaves were run with LeanFinder, Loogle, grep, and LeanSearch and are recorded in `searches.jsonl`; the prior item searches were retained.

What could not be finished: nothing.
