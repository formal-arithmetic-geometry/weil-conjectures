## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-clopen-strict-tower-roos-equivalence.json`: statement node, now split in seven steps. Its statement and statement dependencies are unchanged. The inherited searches are retained and the searches run for this attempt are appended. No Mathlib match for the entire item.
- `citations.json`: 21 verbatim excerpts, one for each dependency used by each proof step.
- `searches.jsonl`: actual msearch log. `bhatt-scholze.txt` is a sandbox-only reading aid produced from the existing PDF.

New nodes: 0. Mathlib leaves created: 0.

## Attachments

None. I searched the project source both for the blueprint tag and for clopen/tower/Roos terminology. `AlgebraicGeometry.Etale.sheaf_clopen_product` in `WeilConjectures/AlgebraicGeometry/EtaleSheafClopenProduct.lean:261` concerns abelian sheaves on the etale site. It does not state the item about arbitrary ring sheaves on the pro-etale site, strict towers, or the specified signed Roos comparisons, and therefore is not an attachment.

## WANTED

None. The needed sources and existing DAG statements are present.

## Problems found and corrected

The input was statement-only; I supplied the proof. There is no statement dispute. In particular, the assertion that termwise products represent derived products is valid here because countable products of arbitrary ring-module sheaves on the pro-etale site are exact. I made that hypothesis verification explicit rather than using the products theorem for arbitrary ringed sites without an exactness hypothesis.

The conclusion about a specified triangle needs both directions and must retain its actual arrows. The proof now reconstructs the converse from the finite sum of zero-inserted component triangles. Naturality of the decomposition is applied to each of the first, middle and connecting arrows. This avoids treating noncanonical cone choices in an ordinary triangulated category as functorial.

The diagonal comparison is checked against the displayed differential and the actual signed connecting map. It is not enough to know that two cone objects are isomorphic. Every proof step is below 2000 characters; the largest is 1291. No argument has been hidden in a new restatement node.

## Unfinished work

None for this stage-1 split. The existing unsplit dependencies remain available for their own dispatched items; I did not split or modify another worker's item. No Lean was written or compiled.

## Not duplicates

No new nodes. The whole-DAG and whole-blueprint searches found the existing ringed module gluing and unbounded derived localization nodes, which are cited directly. The existing exact-countable-product, derived-product-core, exact-functor and finite-sums nodes provide the other non-elementary inputs. Blueprint searches for clopen, clopen tower, strict tower and mapping cone found no blueprint node stating this entire strict-tower comparison with its projection and signed-map normalizations. The item's existing blueprint ancestry is retained, with `same_as: []`.

## Review by Q90

I read the stage-1 brief, the stage contract, the three blueprint levels in SETUP, GOAL, and delivery-errors B through E. I read the smooth-purity chapter and sk-def-purity-conv unit, the current blueprint section-invariant definition (under sec-six-functors-basics/sk-def-purity-conv in main-20261015), and the item's recorded ancestry through finite-clopen derived decomposition and Roos integral descent. This item implements the strict-tower portion of that recorded expansion; it does not change the unit or chapter route.

For the item I read Stacks `derived.tex`, Tag 08TC (`definition-derived-limit`), Tag 07KC (`lemma-products`), Tag 015F (`lemma-right-derived-exact-functor`), the cone definition Tag 014E, and the finite-sum assertion Tag 0CRG (`lemma-products-sums-shifts-triangles`). I also read `sites.tex` Tags 04TQ, 04TR and 04TS on gluing, and Bhatt--Scholze Propositions 3.1.9, 3.2.3(1) and 4.2.8 in the existing PDF. The last three apply to any scheme, so the item does not need finite type, affineness, Noetherianity or a constant coefficient ring. They explain precisely why the existing module-sheaf exact-product node applies. The explicit strict calculations are agent-written applications of these sources and are marked accordingly. No new nodes need separate sources, and no SGA source is used.

In step 1 I checked the actual statement of `lem-pur-clopen-ringed-module-gluing`: it provides an additive exact equivalence for arbitrary commutative ring sheaves on a finite disjoint clopen cover, the exact sectionwise formula, and the specified unit and counit. Our schemes, rings, sites and finite partition satisfy all those hypotheses. Applying its natural maps to the differentials and transitions really gives strict maps by the equation in `def-weil-inverse-system`. The argument is degreewise functoriality, so it creates no additional mathematical lemma.

In step 2 I checked that `lem-weil-proetale-countable-products-exact` states existence and the sectionwise formula for exactly these module categories. The universal property in `def-weil-category-product` makes equality after every projection sufficient. `def-weil-tower-transition-endomorphism` gives the exact nth-coordinate formula used, while the gluing node gives the double-product expression. The product permutation is inverted explicitly; it fixes each pair of indices. The formulas preserve the differentials, actions and tower maps because they do so coordinate by coordinate.

In step 3 I compared the displayed two-summand differential directly with `def-weil-strict-roos-model`. Both orders are the target-copy in degree m-1 followed by the source-copy in degree m. The diagonal alpha commutes with that differential by the transition identity of step 2; the diagonal inverse uses alpha inverse. For tower maps, the naturality equation is checked after each nth projection. For the first map the second coordinate gives p beta = alpha p, and the connecting-map check is beta[1](-z,0)=(-alpha z,0). Thus the negative sign is actually verified. These are morphism equalities before localization, not claims about detecting derived morphisms by sections.

In step 4 I opened `lem-pur-clopen-unbounded-derived-localization` and checked that its statement supplies inverse triangulated unbounded equivalences and localization comparisons for this same arbitrary ring sheaf and clopen cover, with no boundedness assumption. Applying the localization functor to the chain comparison and inverse preserves the two inverse equations and every normalized-map equation. The proof does not assume a functorial choice of cones in the triangulated category.

In step 5 the exact-product hypothesis required by `lem-weil-derived-countable-products-core` is supplied explicitly for X and every component by the pro-etale exact-product node. Its statement says the localized actual product cone is a limit cone; hence its actual projections, not merely its product object, are retained. This identifies the middle arrow with the transition endomorphism required by `def-weil-derived-limit`. I checked that the index is countable and that the module categories use the fixed site and module universes.

In step 6 the forward implication uses the triangulated part of the existing derived equivalence. For the converse, the module gluing node makes zero insertion exact (insertion is exact componentwise and G is exact). The statement of `lem-sf-exact-functor-derived-triangulated` then makes its derived functor triangulated. The statement of `lem-weil-finite-sums-distinguished-triangles` supplies a distinguished finite sum, with its specified shift identification. The derived decomposition node supplies the natural isomorphism from that sum to the identity; I use its naturality on all three triangle maps, and its degreewise origin for shift compatibility. TR1, explicitly present in `def-weil-triangulated-category`, then gives that the original specified triangle is distinguished. These nodes say exactly what is taken from them; `def-weil-derived-limit` is used only for the property it defines, not for an existence or uniqueness theorem.

In step 7 I checked the actual empty and zero-ring clauses in both gluing and derived-localization statements. An empty partition forces an empty scheme. All complexes and maps are then unique in the zero categories, and TR1 supplies the unique distinguished triangle. I also tested a singleton partition (all comparisons become identities), two components (the product permutation fixes each (i,n) coordinate), empty extra components, a zero coefficient sheaf, and towers with zero or identity transitions. The differential and signed connecting-map identities continue to hold without any surjectivity requirement on the transitions. No hidden Mittag--Leffler hypothesis is used.

I checked C1 and C4 against every cited statement and copied the precise relevant text into citations.json. I checked B1--B10: there are no new nodes to misstate, duplicate or misclassify, and all searches recorded for this attempt actually ran through msearch. I read the returned search hits: complex-shape restrictions and Zariski module restrictions have different meanings, while the generic additive-functor mapping-cone isomorphism is only an ingredient. None gives the full item by one-line specialization. I checked D1--D5 by keeping the strict equivalence and all coordinate computations in the item's steps. I checked E1--E7 using the hypotheses and small cases above. The generic off-unit product and triangulated tool uses are declared in split_report.tool_uses; they do not replace the unit's geometric route.

The server-side `review_split` invocation passed with 0 new nodes before the full delivery dry run. The full dry run and delivery are the remaining mechanical actions.
