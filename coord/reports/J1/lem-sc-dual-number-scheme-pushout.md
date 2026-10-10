# Stage-1 report: lem-sc-dual-number-scheme-pushout

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-dual-number-scheme-pushout.json`: split the item; no new nodes and no Mathlib leaves created.
- `citations.json`: exact statement excerpts for all proof citations.

## Attachments

None. I found no sorry-free WeilConjectures declaration stating the finite pushout.

## Sources and corrections

I read Stacks Tag 0B2B (Varieties, tangent-space lemma) and Tag 01J6 (Schemes, morphisms from spectra of local rings) on the Stacks Project website. The local `literature/stacks-project/` material has not been regenerated in this checkout. Tag 0B2B states the two-copy case and explicitly invokes the ring result and 01J6. Its finite-copy extension is the coefficientwise calculation written in step 1. The item's original proof was empty; its statement and blueprint reference were already precise. Searches of the DAG, blueprint index, and pinned Mathlib found no duplicate of the complete item. The existing 01J6 node is a Mathlib leaf. No new node was warranted for the two-line ring calculation.

The n=1 case is the identity, and n=2 gives the Stacks square. In characteristic 2 the multiplication formula is still valid; no division by 2 is used. The common reduction condition is necessary: without it, the proposed ring map into the fibre product does not exist. The field assumption makes the square-zero extensions local.

## Review by J1

I checked step 1 directly against the algebra in Stacks 0B2B: the chosen maps are the coordinate projections, and multiplication in the proposed fibre product agrees in every coefficient. `def-sc-dual-numbers` states the dual-number object and its square-zero generator; it is the only node step 1 cites. For steps 2 and 3 I opened `lem-weil-pbc-morphism-from-spec-local-ring` and verified that its statement gives a bijection for every scheme X and every local ring B, with the closed-point image and local stalk map. Both D and A_n meet that local-ring hypothesis by step 1. Equality after c gives the same point and residue map, so the tuple of local maps has the common scalar coordinate required for A_n. Step 3 uses injectivity of the coordinate embedding proved in step 1 and injectivity of the cited bijection. The exact used clauses are quoted in `citations.json`. I checked the item against delivery-errors B-E: no new statement duplicates the item, no hidden non-elementary fact is left uncited, and the source's two-copy assertion is extended by an explicit finite coefficient calculation. I corrected the empty proof and supplied the missing scheme correspondence citation. The original node's `blueprint.from.place` already identifies the tangent-vector paragraph, and the blueprint search found no same-as node.

## Not duplicates

No new nodes were created.

## Unfinished

None.

## Second reading by J1

- Item statement: checked against Stacks Tag 0B2B (`varieties-lemma-tangent-space`) and its use of Schemes Tag 01J6 (`lemma-morphism-from-spec-local-ring`); the field, common closed-point, finite `n \ge 1`, and universal-property hypotheses agree. The coefficient algebra, maps `j_i`, and reduction map `c` are stated explicitly, so the statement is self-contained.
- Node audit: the item node is an existing DAG node being completed, not a newly created supporting node; no duplicate or restatement node was added, and no Mathlib leaf was claimed. Its definition dependencies are exactly the scheme conventions, dual numbers, and affine spectrum nodes.
- Step 1: checked the coefficientwise identification of `A_n` with the finite fibre product of `D \to K` against the ring calculation in Tag 0B2B. The square-zero ideal and field quotient give locality directly; this is elementary from `def-sc-dual-numbers` and definitions.
- Step 2: checked the cited statement of `lem-weil-pbc-morphism-from-spec-local-ring` supplies the point/local-ring-map bijection for each local source. Equality after `c` forces the same point and residue map, and the fibre-product calculation gives the unique local map to `A_n`; no unstated theorem is used.
- Step 3: checked both existence restrictions and uniqueness through the same 01J6 correspondence and joint injectivity of the coordinate projections. The induced map on local rings is the stated projection, so the cited node says exactly what the step needs.
- Edge cases and hypotheses: `n=1` reduces to `A_1=D`, `n=2` is the Tag 0B2B square, a field target gives the expected unique constant map, and the empty scheme has no input tuple, so the universal property is vacuous. Characteristic 2 is harmless because no division is used. The common reduction condition is necessary for the fibre-product map.
- Changes made in this second reading: none to the mathematics or citations; the existing worker review was supplemented with this per-step/per-node audit required by the delivery contract.
