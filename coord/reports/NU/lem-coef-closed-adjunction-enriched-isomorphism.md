# Worker report: lem-coef-closed-adjunction-enriched-isomorphism

## Files written

- `dag/nodes/sec-six-functors/lem-coef-closed-adjunction-enriched-isomorphism.json`: existing statement, now split into five steps. No change to the statement or its hypotheses. Mathlib verdict: no exact match or one-line specialization.
- `citations.json`: one verbatim statement extract for every use in every proof step.
- `report.md`: this report. The search command generated `searches.jsonl`; the item's previous search history is retained, with six searches from this session appended.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record was changed: this auxiliary item is not its unit's key node.

## Attachments

None. I searched the project source `lean/WeilConjectures/` for the exact blueprint tag and by the closed-adjunction, enriched, internal-Hom, tensor-left-adjoint and comparison notions. The tag has no hit there. The pro-etale internal-Hom comparison file proves pullback/internal-Hom statements with geometric and monoidal assumptions, not this abstract tensor-bifunctor assertion. The existing DAG naturality node supplies only naturality, not invertibility, and is used as such.

## WANTED

None. The necessary adjunction conventions are present in the Stacks source and the blueprint sources are present locally. The proof is explicitly agent-written; I do not attribute the full result to a Stacks tag.

## Corrections and scope

The item was statement-only. Its statement is well-typed and true with the stated tensor bifunctors and natural closed bijections. I preserved it verbatim. The old top-level `source` names `sites-cohomology.tex` as the location of an agent extraction, not a literal theorem. That field belongs to the maintainer and was retained. The proof sources and proof origin now identify Categories Tag 0037 (`definition-adjoint`) and the formulas immediately after it, with the closed-bifunctor argument explicitly attributed to the agent.

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, the ancestor node, the original master proof of `prop-coef-integral-exceptional-adjoint` (paragraph 2, its mapping-complex chain), and the current `main-20261015` file (now under `sk-thm-sf-package`), which states the integral adjunction but contains no proof. This split supplies the isolated categorical calculation requested by the parent; it does not replace the integral coefficient route. No forbidden SGA route is used.

## Not duplicates

No new node was created. I searched the full DAG and the imported-blueprint index for closed adjunctions, tensor preservation, internal-Hom adjunctions and the enriched-isomorphism title. `lem-coef-closed-adjunction-naturality` already gives the exact naturality equation, so step 5 cites it. `lem-pod-hom-chain-counit-formula` concerns a geometric exceptional adjunction and a projection map, with different hypotheses. `lem-sfb-projection-internal-hom-formal` requires two oppositely oriented adjunctions and a projection formula; it is not this tensor-preserving-left-adjoint assertion without those extra data. The coyoneda isomorphism lemma could package a dual Hom-test, but the three-line inverse argument is elementary and creates no node.

## Review by NU

I checked the split against delivery-errors B through E with the statements and sources open. I read Categories Tag 0037, label `definition-adjoint`, and the following discussion at `categories.tex:3344` onward: it gives both directions of the adjunction bijection, its naturality, the unit and counit, and the precise formulas used below. I checked Tag 0014, label `definition-category`, against the identity and associativity laws in `def-nagata-category`. There are no new-node source claims to review.

Step 1 uses only the identity laws stated in `def-nagata-category`, evaluation as the inverse image of the identity, and the assumed test-object naturality of the closed bijections. Substituting a morphism into that naturality equation gives the written inverse-transpose formula. It does not require a separate closed-monoidal or dualizability theorem.

Step 2 uses the statement of `lem-weil-pbc-adjunction-of-natural-bijection`, which explicitly supplies natural Hom bijections and the formula for their inverses in terms of the counit. I checked all six Hom sets in order. In particular the middle arrow precomposes with `mu`, not its inverse; its inverse precomposes with `mu` inverse. Both closed-bijection arrows are hypotheses of the item. The composite is bijective because every factor is bijective.

Step 3 uses the same adjunction node's source-naturality equation and its formula involving the unit. Naturality of `mu` at `(t,1_P)` and of the closed transpose in its test object identify the middle expression with `b` composed with `F(t)`. The final three equalities give exactly postcomposition by the specified `delta`. This check matters: arbitrary abstract isomorphism of the two objects would not prove this assertion. Every map in the first displayed equality has source `F(T) tensor F(P)` and target `F(V tensor P)`.

Step 4 invokes only the category laws in `def-nagata-category` and steps 2--3. Surjectivity at `T=W=G(J)` gives a right inverse of `delta`; injectivity at `T=V` turns the displayed equality into a left inverse. Both test objects belong to C, so no smallness, representability, product, or full-faithfulness hypothesis has been imported. This is the elementary inverse argument itself, not an uncited appeal to Yoneda.

Step 5 cites the exact statement of `lem-coef-closed-adjunction-naturality`. I compared its definitions of `b` and `delta` and every hypothesis to the item: the same categories, tensor bifunctors, contravariant/covariant Hom bifunctors, natural closed bijections, natural isomorphisms `mu`, unit and counit. Its displayed delta square is literally the square needed here, as the quote in `citations.json` records. The cited node's proof dependencies are only the category and adjunction leaves, so there is no cycle through this item or the derived-system parent. Pointwise invertibility from step 4 and these squares are precisely a natural isomorphism. No new off-unit tool use is needed.

I checked small cases as well. For the identity adjunction with the identity tensor comparison, the chain reduces to the inverse closed bijection followed by itself and `delta` is the identity. For Set with Cartesian product and `P` empty, both internal Hom objects are terminal and the specified map is its identity; empty targets and nonempty P also present no obstruction. In the terminal category every arrow in the calculation is the unique isomorphism. As a non-fully-faithful example, the constant-terminal left adjoint on Set has constant-terminal right adjoint and preserves binary products; both sides are terminal. Thus the proof does not accidentally use full faithfulness. The calculation never reassociates tensor factors or introduces a tensor unit. All five steps are below 2000 characters and none hides a separate comparison theorem.

The six new Mathlib searches are exactly those recorded by `msearch.py`. I read all returned hits, including both semantic phrasings. `ihom.adjunction` and `internalHomAdjunction₂` provide a closed adjunction in one monoidal category. I read `Monoidal/Closed/Basic.lean` around `ofEquiv`: it assumes `F.IsEquivalence`. I read `Monoidal/Closed/Functor.lean`: `expComparison` and its Frobenius results assume Cartesian monoidal categories and concern other comparison maps. The second semantic search also returned `Adjunction.comp_homEquiv`, a formula for composing adjunction bijections, and rigid tensor-Hom results requiring dual objects. These are ingredients or stronger-assumption special cases, not one-line specializations proving this item. The old searches are retained as historical evidence, and no unperformed search has been invented.

The quotation file was checked against the actual statement strings. No theorem was moved into a new node, no definition contains hidden data, and no new statement needs an independent small-case check. The statement, existing metadata and blueprint ancestry are preserved; the already precise ancestry place is retained and `same_as` was searched. Nothing remains unfinished in the split.
