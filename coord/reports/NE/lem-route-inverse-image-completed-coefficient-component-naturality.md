## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-route-inverse-image-completed-coefficient-component-naturality.json` — the item, split with no new nodes; Mathlib searches found no exact or one-line Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.
- `searches.jsonl` — the four Mathlib searches run for this item.

Attachments: none. The Lean declaration remains sorried, so it is not an attachment. The proof cites the existing node `lem-cbc-finite-constant-map-naturality`.

WANTED: none.

The imported item was a provisional sentence that did not define the coefficient system, its limit projections, or the constant-section maps. I replaced it with a self-contained statement for finite quotient rings, the inverse systems of constant pro-etale ring sheaves, their completed limits, the canonical inverse-image maps, and the component equation. The Lean signature and its composition orientation were checked against `Sheaf/AlgebraicGeometry/ProEtale/InverseImagePullbackComparison.lean`. The theorem's original source field cited Deligne's Weil II, but the actual argument is the Stacks finite-limit/constant-sheaf route (Tags 03CO and 0H7J), so the source and proof origin now cite that route.

No new node was created because the required non-elementary coefficient-map fact is already exactly stated by `lem-cbc-finite-constant-map-naturality`; the limit projection equation is supplied by `def-pur-sheaf-inverse-limit`, and inverse-image/constant-section data by `def-weil-proetale-inverse-image`. The Mathlib searches found only ordinary adic-completion lemmas, which do not cover the project-specific pro-etale RingCat construction.

## Review by NE

I read the live Lean declaration and the definitions immediately preceding it in `InverseImagePullbackComparison.lean`, including `inverseImageCompletedCoefficientComponent` and the `integralCoefficientSheafSystem` projections. I also read the statements of `def-weil-l-adic-coefficient-extension`, `def-weil-completed-integral-coefficients`, `def-pur-sheaf-inverse-limit`, `def-weil-proetale-inverse-image`, and `lem-cbc-finite-constant-map-naturality` in the DAG. The item statement introduces the same finite rings, schemes, isomorphism, inverse systems, projections, and canonical constant-section maps as the Lean construction.

Step 1 uses only the limit-cone equation for the projections and functoriality of inverse image; the cited limit and inverse-image nodes state those constructions. Step 2 uses the quotient homomorphism $A_{E,b}\to A_{E,a}$ and applies the existing finite constant-map naturality node. Its statement gives exactly the square needed after taking $B=A_{E,a}$ and $C=A_{E,b}$ (with the opposite-index direction), and the coefficient-extension node supplies finiteness and commutativity of these quotient rings. Step 3 is reassociation and substitution, with the completed-coefficient node supplying the projection notation. Every citation quote in `citations.json` was checked verbatim against its node statement.

I tested the orientation on an adjacent transition, on an identity morphism, and on the zero/terminal sheaf case: the cone equation reduces to the identity law in each case. I also checked that no new node duplicates an existing statement and that the blueprint ancestor and `same_as` fields are filled. Nothing remains unfinished in the stage-1 split.

The cross-unit citation of `lem-cbc-finite-constant-map-naturality` is explicitly declared in `split_report.tool_uses`: Step 2 uses its finite constant-section square as a generic coefficient tool because the current unit has no replacement for that coefficient lemma.
