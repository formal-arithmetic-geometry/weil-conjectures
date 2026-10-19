# Stage 1 report: lem-exc-relative-adjoint-open-origin

Files written:

- `dag/nodes/sec-smooth-purity/lem-exc-relative-adjoint-open-origin.json`: statement, split proof, proof dependencies, blueprint metadata, and status `split`; no new nodes and therefore no Mathlib leaves.
- `citations.json`: 16 step-to-node verbatim citations.
- `report.md`: this report.

Attachments: none. No existing Lean declaration states this item exactly; the source search found only the general `rightDerivedUpperShriekAdjunction` declarations and no sorry-free project declaration with the item tag.

WANTED: none.

The imported statement is retained. It is the bounded-below witness obligation extracted from Step 8 of the retained repaired proof of `prop-exc-base-change-proper`. The proof does not assert an isomorphism between the two displayed etale complexes and does not add an unrestricted pro-etale adjunction.

The required Mathlib searches for the item were run with `msearch.py`: LeanFinder (finite-coefficient exceptional inverse image and etale-origin witnesses), Loogle (`DerivedCategory, IsGE`), grep (`exceptional|etaleOrigin|etale.*origin|origin.*etale` in `AlgebraicGeometry`), and LeanSearch (proper exceptional adjoint and open restriction). The hits were generic scheme/module or derived-category declarations and did not match this fixed-coefficient site-comparison statement; the Loogle `IsGE` query returned an unknown identifier, so it is recorded as no match without using it as evidence of absence.

## Review by NJ

I read the current item node, the `sk-prop-sf-existence` unit and its chapter, the main-20261015 Step 8 source, and the full statements of every cited node. Step 1 checks that the open immersion is finite type, that finite type survives composition and base change, that properness survives the fibre-product base change, and that the pulled-back open is an open immersion. The finite-type dimension bound then supplies identity-open compactifications to which `thm-sf-ambient-adjoint-class` applies. Step 2 uses the bounded-below typing clause of `def-weil-exceptional-inverse-image`; I verified that exact inverse image on etale module sheaves and the exact-functor bound preserve the lower cohomological bound, so both displayed etale complexes really lie in `D+`. Step 3 explicitly composes the comparison adjunction unit with the supplied `alpha` and uses the defining formula for `Rf!`; I checked the direction of the unit and that full faithfulness applies to arbitrary bounded-below constant-module complexes. Step 4 uses the canonical square comparison `nu_U^* u_et^{-1} ≅ u_proet^{-1} nu_V^*` on the fibre-product square, then applies it to the two etale complexes; the second witness also uses the same comparison unit after restricting `K0` along `g`. Step 5 checks the definition of the witnessed full category and records that the two witnesses are separate objects. I corrected the initial draft's malformed `f'^!` notation and rewrote that step to use the relative exceptional expression exactly.

No long proof step exceeds 2000 characters. The edge cases of an empty open or empty fibre product reduce to zero complexes, and identity open immersions reduce the comparison maps to the comparison unit. No new node was created, so there is no duplicate pair to report.

What could not be finished: nothing at the stage-1 level; the required dry run and delivery remain to be executed.
